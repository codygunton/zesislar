"""Tier replay with a fake agent (no model, no Rocq): wave bookkeeping, the repeated-prompt rule, retry
prompts, the tier override guard, session usage, and the routing rule on synthetic results."""
import asyncio
import json
from pathlib import Path
import sys
import tempfile
import unittest

HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE))
import dispatch_kernel  # noqa: E402
import replay  # noqa: E402
import store  # noqa: E402

HEADER = ["Require Import ZesuSsz.Automation2.All.", "Local Open Scope Z_scope."]
SLOT = "(* PROOF-SLOT: replace this line and the Admitted below with the proof script and Qed. *)\nAdmitted.\n"
PROVED = json.dumps(dict(verdict="proved", proof="intros. lia.\nQed."))


def make_corpus(root, statements, classes=None):
    """A corpus dir as `replay.py corpus` writes it, for known-set goals with the given statements."""
    corpus = Path(root) / "corpus"
    rows, goals = [], []
    for n, statement in enumerate(statements, 1):
        gid = "k%03d" % n
        name = "replay_" + gid
        d = corpus / "goals" / gid
        d.mkdir(parents=True)
        (d / "goal.v").write_text("%s\n\nLemma %s :\n  %s.\nProof.\n%s" % ("\n".join(HEADER), name, statement, SLOT))
        task = corpus / "tasks" / "similar" / ("%s.md" % gid)
        task.parent.mkdir(parents=True, exist_ok=True)
        text = "# Pure goal %s\n\n%s\n" % (gid, statement)
        task.write_text(text)
        cls = (classes or {}).get(gid, "PURE-linear")
        rows.append(dict(id=gid, set="known", name=name, store_id=store.goal_id("replay", "%04x" % n, statement),
                         statement_sha256=replay.sha(statement), reparse="exact", readable_bytes=10,
                         prompts=dict(similar=dict(path=str(task), bytes=len(text), sha256=replay.sha(text),
                                                   context_items=["similar"], similar=["residual_x"], fits=True)),
                         **{"class": cls}))
        goals.append(dict(id=gid, name=name, statement=statement, reparse="exact", readable="", binders=[], counts={}))
    (corpus / "MANIFEST.json").write_text(json.dumps(dict(block="0000", bank="/nonexistent", goals=goals)))
    (corpus / "CORPUS.json").write_text(json.dumps(dict(schema="oblig-replay-corpus/1", head="h", bank="/nonexistent",
                                                        ocamlpath="", rows=rows)))
    return corpus


class FakeHandle:
    count = 0

    def __init__(self, prompt, reply):
        FakeHandle.count += 1
        self.id = "Fake%d" % FakeHandle.count
        self.prompt, self.reply, self.finished = prompt, reply, False

    def done(self):
        return self.finished

    def wait(self, timeout=None):
        self.finished = True
        return self.reply


class Kernel:
    """The kernel helpers dispatch_kernel uses: agent, wait, tool."""

    def __init__(self, reply=PROVED):
        self.reply = reply
        self.spawned = []
        self.writes = []
        kernel = self

        class Tool:
            async def write(self, args):
                kernel.writes.append(args)
        self.tool = Tool()

    def agent(self, prompt, agent=None, label=None):
        handle = FakeHandle(prompt, self.reply(prompt) if callable(self.reply) else self.reply)
        self.spawned.append((agent, label, handle))
        return handle

    def wait(self, handles, raise_errors=True):
        return [h.wait() for h in handles]

    def install(self):
        dispatch_kernel.agent = self.agent
        dispatch_kernel.wait = self.wait
        dispatch_kernel.tool = self.tool
        dispatch_kernel._STATE.update(overrides={}, live=[], current={})


class WaveTests(unittest.TestCase):
    def setUp(self):
        self.tmp = tempfile.TemporaryDirectory()
        self.corpus = make_corpus(self.tmp.name, ["forall (x : Z), x < x + 1", "forall (y : Z), y <= y",
                                                  "forall (z : Z), z = z"])
        self.kernel = Kernel()
        self.kernel.install()
        dispatch_kernel.SESSIONS = Path(self.tmp.name) / "sessions"

    def tearDown(self):
        self.tmp.cleanup()

    def events(self, tier="haiku-low", recipe="similar"):
        return store.read_events(replay.store_dir(self.corpus, recipe, tier))

    def test_wave_bookkeeping(self):
        summary = dispatch_kernel.run_wave(self.corpus, "haiku-low", concurrency=2)
        self.assertEqual(summary["started"], 3)
        self.assertEqual(summary["verdicts"], {"proved": 3})
        self.assertEqual({a for a, _, _ in self.kernel.spawned}, {"sonic"})
        d = replay.attempt_dir(self.corpus, "similar", "haiku-low", 1)
        for gid in ("k001", "k002", "k003"):
            self.assertEqual((d / "answers" / ("%s.v" % gid)).read_text(), "intros. lia.\nQed.\n")
            meta = json.loads((d / "answers" / ("%s.json" % gid)).read_text())
            self.assertEqual((meta["verdict"], meta["tier"], meta["answer_bytes"]), ("proved", "haiku-low", len(PROVED)))
        wave = json.loads((d / "WAVE.json").read_text())
        self.assertIsNone(wave["k001"]["tokens_in"])
        self.assertTrue(wave["k001"]["agent_id"].startswith("Fake"))
        running = [e for e in self.events() if e["state"] == "running"]
        self.assertEqual(len(running), 3)
        prompt = (d / "prompts" / "k001.md").read_text()
        first = next(e for e in running if e["id"].endswith(replay.sha("forall (x : Z), x < x + 1")[:16]))
        self.assertEqual((first["prompt_sha256"], first["prompt_bytes"], first["attempt"]),
                         (replay.sha(prompt), len(prompt.encode()), 1))
        self.assertEqual(self.kernel.spawned[0][2].prompt, prompt)

    def test_repeated_prompt_is_not_sent(self):
        dispatch_kernel.run_wave(self.corpus, "haiku-low")
        again = dispatch_kernel.run_wave(self.corpus, "haiku-low")
        self.assertEqual(again["started"], 0)
        self.assertEqual(len(again["rejected"]), 3)
        self.assertIn("already sent to tier haiku-low", again["rejected"][0][1])
        self.assertEqual(len(self.kernel.spawned), 3)
        other = dispatch_kernel.run_wave(self.corpus, "opus-medium")
        self.assertEqual(other["started"], 3)
        self.assertEqual(self.kernel.spawned[-1][0], "task")

    def test_verdicts_other_than_proved_are_failures(self):
        replies = {"k001": dict(verdict="give_up"), "k002": dict(verdict="need_context", needs=["Z.lt_irrefl"])}

        def reply(prompt):
            gid = prompt.split()[3]
            return json.dumps(replies[gid]) if gid in replies else "no json here"
        self.kernel.reply = reply
        summary = dispatch_kernel.run_wave(self.corpus, "haiku-low")
        self.assertEqual(summary["verdicts"], {"give_up": 1, "need_context": 1, "malformed": 1})
        failed = {e["class"] for e in self.events() if e["state"] == "failed"}
        self.assertEqual(failed, {"give_up", "need_context", "malformed"})

    def test_retry_prompt_differs_and_carries_the_errors(self):
        dispatch_kernel.run_wave(self.corpus, "haiku-low")
        d = replay.attempt_dir(self.corpus, "similar", "haiku-low", 1)
        (d / "CHECK.json").write_text(json.dumps({"k001": {"result": "FAIL"}, "k002": {"result": "PASS"}}))
        (d / "feedback" / "k001.txt").write_text("FAIL\nError: The variable x was not found.\n")
        store.append(replay.store_dir(self.corpus, "similar", "haiku-low"), store.event(
            id=json.loads((self.corpus / "CORPUS.json").read_text())["rows"][0]["store_id"], function="replay",
            kind="goal", state="failed", tier="haiku-low", attempt=1, prompt_sha256=replay.sha(
                (d / "prompts" / "k001.md").read_text()), **{"class": "compile_error"}))
        summary = dispatch_kernel.retry_wave(self.corpus, "haiku-low")
        self.assertEqual(summary["started"], 1)
        retry = replay.attempt_dir(self.corpus, "similar", "haiku-low", 2) / "prompts" / "k001.md"
        first = (d / "prompts" / "k001.md").read_text()
        text = retry.read_text()
        self.assertTrue(text.startswith(first))
        self.assertNotEqual(replay.sha(text), replay.sha(first))
        self.assertIn("The variable x was not found", text)
        self.assertIn("intros. lia.", text)
        self.assertEqual(self.kernel.spawned[-1][2].prompt, text)
        with self.assertRaises(replay.ReplayError):
            replay.prepare_retry(self.corpus, "haiku-low", attempt=3)

    def test_mechanical_runs_no_model(self):
        summary = replay.run_wave(self.corpus, "mechanical", None)
        self.assertEqual((summary["started"], summary["verdicts"]), (3, {"proved": 3}))
        d = replay.attempt_dir(self.corpus, "none", "mechanical", 1)
        self.assertIn("LinearFirstLia.zesu_lia_linear_first3", (d / "answers" / "k001.v").read_text())
        self.assertEqual(self.kernel.spawned, [])
        self.assertEqual(replay.run_wave(self.corpus, "mechanical", None)["started"], 0)


ENVELOPE = json.dumps({"architecture": "one closed fact", "files": [],
                       "summary": json.dumps({"verdict": "proved", "proof": "intros. lia.\nQed."})})


class DefectTests(unittest.TestCase):
    """The three defects of the first waves: expired handles, enveloped replies, retries that did not fit."""

    def setUp(self):
        self.tmp = tempfile.TemporaryDirectory()
        self.corpus = make_corpus(self.tmp.name, ["forall (x : Z), x < x + 1", "forall (y : Z), y <= y"])
        self.kernel = Kernel()
        self.kernel.install()
        dispatch_kernel.SESSIONS = Path(self.tmp.name) / "sessions"
        self.rows = json.loads((self.corpus / "CORPUS.json").read_text())["rows"]

    def tearDown(self):
        self.tmp.cleanup()

    def test_expired_handle_counts_as_finished_and_waves_prune(self):
        class Expired:
            def done(self):
                raise RuntimeError("unknown agent handle x; result expired")
        dispatch_kernel._STATE["live"] = [(replay.tier_row("haiku-medium"), Expired())]
        self.assertEqual(dispatch_kernel._unfinished("scout", "haiku-high"), [])
        self.assertEqual(dispatch_kernel._STATE["live"], [])
        dispatch_kernel.run_wave(self.corpus, "haiku-low")
        self.assertEqual(dispatch_kernel._STATE["live"], [])

    def test_answer_inside_an_envelope(self):
        self.assertEqual(replay.parse_reply(ENVELOPE)[0]["verdict"], "proved")
        fenced = json.dumps({"summary": "text\n```json\n{\"verdict\": \"give_up\"}\n```"})
        self.assertEqual(replay.parse_reply(fenced)[0], {"verdict": "give_up"})
        self.assertEqual(replay.parse_reply(json.dumps(json.dumps({"verdict": "give_up"})))[0], {"verdict": "give_up"})
        self.assertEqual(replay.parse_reply({"files": [{"note": ENVELOPE}]})[0]["verdict"], "proved")
        self.assertIsNone(replay.parse_reply(json.dumps({"architecture": "x", "summary": "no answer"}))[0])
        self.kernel.reply = ENVELOPE
        self.assertEqual(dispatch_kernel.run_wave(self.corpus, "haiku-low")["verdicts"], {"proved": 2})

    def test_rescore_keeps_the_log_append_only(self):
        self.kernel.reply = "no answer here"
        dispatch_kernel.run_wave(self.corpus, "haiku-low")
        run = replay.store_dir(self.corpus, "similar", "haiku-low")
        before = (run / store.LOG).read_text()
        d = replay.attempt_dir(self.corpus, "similar", "haiku-low", 1)
        (d / "answers" / "k001.raw").write_text(ENVELOPE)
        (d / "answers" / "k002.raw").write_text(json.dumps({"summary": json.dumps({"verdict": "give_up"})}))
        self.assertEqual(replay.rescore(self.corpus, "haiku-low"), {"proved": 1, "give_up": 1})
        after = (run / store.LOG).read_text()
        self.assertTrue(after.startswith(before))
        self.assertEqual((d / "answers" / "k001.v").read_text(), "intros. lia.\nQed.\n")
        # check's final event for the rescored proof is a correction too.
        prompt = (d / "prompts" / "k001.md").read_text()
        replay.append_result(run, store.event(id=self.rows[0]["store_id"], function="replay", kind="goal",
                                              state="closed", tier="haiku-low", attempt=1,
                                              prompt_sha256=replay.sha(prompt)))
        corrections = [json.loads(l) for l in (run / store.LOG).read_text().splitlines()[len(before.splitlines()):]]
        self.assertEqual([(e["state"], e["attempt"]) for e in corrections], [("failed", None), ("closed", None)])
        results = replay.attempt_results(self.corpus, None, replay.load_tiers())[("similar", "haiku-low")]
        self.assertEqual(results[self.rows[0]["store_id"]][1]["result"], "closed")
        self.assertEqual(results[self.rows[1]["store_id"]][1]["result"], "give_up")
        self.assertEqual(replay.rescore(self.corpus, "haiku-low"), {})

    def big_prompts(self, text_bytes):
        """Attempt-1 prompts with a similar-lemma section that fills the bound."""
        d = replay.attempt_dir(self.corpus, "similar", "haiku-low", 1)
        for row in self.rows:
            base = "# Pure goal %s\n\nGOAL-PART %s\n" % (row["id"], "g" * 2000)
            blocks = ["Similarity 0.%d0.\n\n### residual_%d\n\n%s\n" % (n, n, "s" * text_bytes) for n in range(3)]
            text = base + replay.SIMILAR_HEAD + "\n".join(blocks) + replay.answer_form(row["id"])
            (d / "prompts" / ("%s.md" % row["id"])).write_text(text)
        return d

    def test_retry_always_fits_and_keeps_the_goal(self):
        dispatch_kernel.run_wave(self.corpus, "haiku-low")
        d = self.big_prompts(3200)
        self.assertGreater(len((d / "prompts" / "k001.md").read_bytes()), 11000)
        (d / "CHECK.json").write_text(json.dumps({"k001": {"result": "FAIL"}}))
        (d / "feedback" / "k001.txt").write_text("FAIL\nError: " + "e" * 20000)
        (d / "answers" / "k002.json").write_text(json.dumps(dict(verdict="need_context", needs=["a lemma about x"])))
        plan, prompts = replay.retry_plan(self.corpus, "haiku-low")
        self.assertEqual(plan, {"k001": "compile_error", "k002": "missing_context"})
        text = prompts["k001"]
        self.assertLessEqual(len(text.encode()), 12000)
        self.assertIn("GOAL-PART " + "g" * 2000, text)
        self.assertNotIn(replay.SIMILAR_HEAD, text)
        self.assertIn("[... truncated]", text)
        self.assertIn("intros. lia.", text)
        self.assertIn("Your whole reply is that JSON object", text)

    def test_need_context_found_in_the_index_and_already_sent(self):
        dispatch_kernel.run_wave(self.corpus, "haiku-low")
        d = self.big_prompts(3000)
        (d / "answers" / "k001.json").write_text(json.dumps(dict(
            verdict="need_context", needs=["the lemma residual_wanted_1 about bounds", "residual_1 again"])))
        index = dict(entries=[dict(name="residual_wanted_1", statement="forall x : Z, x = x", proof="reflexivity.\nQed.")])
        original = replay.similar.build_index
        replay.similar.build_index = lambda *a, **k: index
        try:
            plan, prompts = replay.retry_plan(self.corpus, "haiku-low")
            self.assertEqual(plan["k001"], "need_context")
            self.assertIn(replay.CONTEXT_HEAD + "### residual_wanted_1", prompts["k001"])
            self.assertLessEqual(len(prompts["k001"].encode()), 12000)
            self.assertEqual(dispatch_kernel.retry_wave(self.corpus, "haiku-low", ids=["k001"])["started"], 1)
            plan, prompts = replay.retry_plan(self.corpus, "haiku-low")
            self.assertEqual(plan["k001"], "already_sent")
            self.assertNotIn("k001", prompts)
        finally:
            replay.similar.build_index = original


class OverrideTests(unittest.TestCase):
    def setUp(self):
        self.kernel = Kernel()
        self.kernel.install()
        self.tmp = tempfile.TemporaryDirectory()
        self.corpus = make_corpus(self.tmp.name, ["forall (x : Z), x = x"])

    def tearDown(self):
        self.tmp.cleanup()

    def test_override_written_and_guarded(self):
        overrides = asyncio.run(dispatch_kernel.set_tier_override("haiku-high"))
        self.assertEqual(overrides["scout"], "anthropic/claude-haiku-5-5:high")
        self.assertEqual(self.kernel.writes[-1]["path"], "cfg://task/agentModelOverrides")
        self.assertEqual(json.loads(self.kernel.writes[-1]["content"])["scout"], "anthropic/claude-haiku-5-5:high")
        with self.assertRaises(replay.ReplayError):
            dispatch_kernel.run_wave(self.corpus, "haiku-medium")
        tier = replay.tier_row("haiku-high")
        dispatch_kernel._STATE["live"].append((tier, FakeHandle("p", "r")))
        with self.assertRaises(replay.ReplayError):
            asyncio.run(dispatch_kernel.set_tier_override("haiku-medium"))
        dispatch_kernel._STATE["live"][0][1].wait()
        asyncio.run(dispatch_kernel.set_tier_override("haiku-medium"))
        self.assertEqual(dispatch_kernel.run_wave(self.corpus, "haiku-medium")["started"], 1)
        self.assertIsNone(asyncio.run(dispatch_kernel.set_tier_override("haiku-low")))

    def test_usage_from_session_log(self):
        sessions = Path(self.tmp.name) / "sessions" / "s" / "parent"
        sessions.mkdir(parents=True)
        rows = [dict(type="session_init", agent="sonic", resolvedModel="anthropic/claude-haiku-5-5:low"),
                dict(type="message", message=dict(role="assistant", usage=dict(input=4, output=19, cacheRead=100,
                                                                                cacheWrite=11536))),
                dict(type="message", message=dict(role="user"))]
        (sessions / "Agent7.jsonl").write_text("\n".join(json.dumps(r) for r in rows) + "\n")
        dispatch_kernel.SESSIONS = Path(self.tmp.name) / "sessions"
        self.assertEqual(dispatch_kernel.usage("Agent7"),
                         dict(tokens_in=11640, tokens_out=19, resolved_model="anthropic/claude-haiku-5-5:low"))
        self.assertEqual(dispatch_kernel.usage("Missing")["tokens_in"], None)


class RoutingTests(unittest.TestCase):
    def setUp(self):
        self.tmp = tempfile.TemporaryDirectory()
        classes = {"k%03d" % n: "PURE-linear" if n <= 4 else "PURE-bitvector" for n in range(1, 9)}
        self.corpus = make_corpus(self.tmp.name, ["forall (x : Z), x + %d = x + %d" % (n, n) for n in range(1, 9)],
                                  classes)
        self.rows = json.loads((self.corpus / "CORPUS.json").read_text())["rows"]

    def tearDown(self):
        self.tmp.cleanup()

    def result(self, tier, closed, recipe="similar", attempt=1, tokens=100):
        run = replay.store_dir(self.corpus, recipe, tier)
        for row in self.rows:
            prompt = "%s-%s-%d" % (tier, row["id"], attempt)
            base = dict(id=row["store_id"], function="replay", kind="goal", tier=tier, attempt=attempt,
                        prompt_sha256=replay.sha(prompt), prompt_bytes=1000, answer_bytes=100, tokens_in=tokens,
                        tokens_out=10)
            store.append(run, store.event(state="running", **base))
            if row["id"] in closed:
                store.append(run, store.event(state="closed", **base))
            else:
                store.append(run, store.event(state="failed", **{"class": "compile_error"}, **base))

    def test_cheapest_tier_at_the_share_wins(self):
        linear = ["k001", "k002", "k003", "k004"]
        self.result("haiku-low", ["k001"])                      # linear 1/4, bitvector 0/4
        self.result("haiku-low", ["k002"], attempt=2)           # linear 2/4 within attempts
        self.result("haiku-medium", ["k005"])                   # bitvector 1/4
        self.result("haiku-high", ["k005", "k006"])             # bitvector 2/4
        self.result("opus-medium", linear + ["k005", "k006", "k007", "k008"])
        data = replay.routing(self.corpus, replay.load_tiers())
        self.assertEqual(data["classes"]["PURE-linear"]["first_tier"], "haiku-low")
        self.assertEqual(data["classes"]["PURE-linear"]["shares"]["haiku-low/similar"]["first"], 1)
        self.assertEqual(data["classes"]["PURE-linear"]["shares"]["haiku-low/similar"]["within"], 2)
        self.assertEqual(data["classes"]["PURE-bitvector"]["first_tier"], "haiku-high")
        self.assertEqual(data["classes"]["PURE"]["first_tier"], "opus-medium")
        self.assertEqual(data["haiku_union"], dict(tiers_run=list(replay.HAIKU), closed=4, of=8, share=0.5,
                                                   sonnet_needed=False))
        self.assertEqual(data["tiers"]["opus-medium/similar"]["tokens_per_closed"], 110)
        self.assertIn("min_share", data["rule"])

    def test_recipe_and_fallbacks(self):
        self.result("haiku-low", ["k001"], recipe="slice")
        self.result("haiku-low", ["k001", "k002", "k005"], recipe="similar")
        data = replay.routing(self.corpus, replay.load_tiers())
        self.assertEqual(data["classes"]["PURE-linear"]["context"], "similar")
        self.assertEqual(data["classes"]["PURE-linear"]["first_tier"], "haiku-low")
        self.assertEqual(data["classes"]["PURE-bitvector"]["first_tier"], "haiku-low")
        self.assertIsNone(data["haiku_union"]["sonnet_needed"])


class HelperTests(unittest.TestCase):
    def test_parse_reply(self):
        self.assertEqual(replay.parse_reply('```json\n{"verdict": "give_up"}\n```')[0], {"verdict": "give_up"})
        self.assertEqual(replay.parse_reply('Here: {"verdict": "false", "counterexample": "x = 1"} done')[0]["verdict"],
                         "false")
        self.assertIsNone(replay.parse_reply("nothing")[0])
        self.assertEqual(replay.parse_reply({"verdict": "proved", "proof": "lia.\nQed."})[0]["verdict"], "proved")

    def test_goal_classes(self):
        self.assertEqual(replay.goal_class("forall (x : Z) (H : Z.lt x 3), Z.lt x 4"), "PURE-linear")
        self.assertEqual(replay.goal_class("forall (w : bv 64), Z.lt (bv_unsigned w) 5"), "PURE-bitvector")
        self.assertEqual(replay.goal_class("forall (l : list Z), length (take 2 l) <> 3"), "PURE-byte-window")
        self.assertEqual(replay.goal_class("forall (a : Args), decodeItemAcceptedFacts a"), "PURE-meaning")
        self.assertEqual(replay.goal_class("forall (a : Args), DecodeMeaningModuloKnownBugs a"), "MEANING")

    def test_counterexample_values(self):
        binders = [dict(name="x", kind="Z"), dict(name="w", kind="bv", width=8), dict(name="b", kind="bool"),
                   dict(name="n", kind="nat"), dict(name="H", kind="prop")]
        self.assertEqual(replay.counterexample_values("x = -3, w = 0x1ff, b = true", binders),
                         dict(x=-3, w=0xff, b=True, n=0))

    def test_base_overrides(self):
        tmp = tempfile.TemporaryDirectory()
        root = Path(tmp.name)
        (root / ".omp").mkdir()
        (root / ".omp/config.yml").write_text("task:\n  agentModelOverrides:\n    scout: a/b:medium\n    sonic: a/c:low\n"
                                              "\nretry:\n  x: 1\n")
        self.assertEqual(dispatch_kernel.base_overrides(root), {"scout": "a/b:medium", "sonic": "a/c:low"})
        tmp.cleanup()


if __name__ == "__main__":
    unittest.main()
