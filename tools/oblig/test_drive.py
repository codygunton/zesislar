"""Production driver with a fake agent and a fake kernel (no model, no Rocq): one round closes a goal and
records its events and tokens, a repeated prompt is refused, a compile error gives a changed retry
prompt, closing a blocker unblocks its dependants, and the scout-tier override guard."""
import asyncio
import json
from pathlib import Path
import sys
import tempfile
import unittest

HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE))
import dispatch_kernel  # noqa: E402
import drive  # noqa: E402
import drive_kernel  # noqa: E402
import report  # noqa: E402
import store  # noqa: E402

F = "fn"
HEADER = "From Coq Require Import ZArith Lia.\nLocal Open Scope Z_scope."
SLOT = "(* PROOF-SLOT: replace this line and the Admitted below with the proof script and Qed. *)\nAdmitted.\n"
GOOD = json.dumps(dict(verdict="proved", proof="intros. lia.\nQed."))
BAD = json.dumps(dict(verdict="proved", proof="intros. wrong_tactic.\nQed."))
GIVE_UP = json.dumps(dict(verdict="give_up"))


def goal_v(name, statement):
    return "%s\n\nLemma %s :\n  %s.\nProof.\n%s" % (HEADER, name, statement, SLOT)


def make_meaning(run, lemmas):
    """RUN/meaning/<name>/ in the residual_loop layout, filed in the store; LEMMAS: (name, deps, body)."""
    rows = []
    for name, deps, body in lemmas:
        d = Path(run) / "meaning" / name
        statement = " ->\n  ".join(["%s_statement" % dep for dep in deps] + [body])
        (d / "goals" / name).mkdir(parents=True)
        (d / "goals" / name / "goal.v").write_text(goal_v(name, statement))
        (d / "tasks").mkdir()
        (d / "tasks" / (name + ".md")).write_text("# Meaning obligation %s\n\n%s\n\n%s\n\n```coq\n%s\n```\n" % (
            name, "Write the proof to answers.", drive.EXACT_HEADING, statement))
        (d / "MANIFEST.json").write_text(json.dumps(dict(
            block="meaning", function=F, bank="/nonexistent", caller=str(d / "HEADER.v"),
            goals=[dict(id=name, name=name, deps=deps, statement=statement, reparse="exact", binders=[], counts={})])))
        goal = d / "goals" / name / "goal.v"
        state, cls = ("blocked-on", store.meaning_id(F, deps[0])) if deps else ("derived", None)
        rows.append(store.event(id=store.meaning_id(F, name), function=F, kind="meaning", state=state,
                                **{"class": cls}, artifact=store.artifact_of(goal)))
    store.append(run, rows)


class FakeKernel:
    """drive.Kernel without Rocq: an answer passes when it uses `lia` (mechanical never passes)."""

    def __init__(self):
        self.checked, self.falsified = [], []

    def check(self, d, gids, jobs):
        out = {}
        for gid in gids:
            text = (Path(d) / "answers" / (gid + ".v")).read_text()
            verdict = "PASS" if "lia." in text and "LinearFirstLia" not in text else "FAIL"
            status_path = Path(d) / "goals" / gid / "STATUS.json"
            status = store.read_json(status_path, {"attempts": [], "result": "OPEN"})
            status["attempts"].append(dict(sha256=drive.rl.sha(text), result=verdict))
            status["result"] = "PASS" if verdict == "PASS" else status["result"]
            status_path.write_text(json.dumps(status))
            if verdict == "PASS":
                (Path(d) / "goals" / gid / "proof.v").write_text(text)
            (Path(d) / "feedback").mkdir(exist_ok=True)
            (Path(d) / "feedback" / (gid + ".txt")).write_text(
                "PASS\n" if verdict == "PASS" else "FAIL\nError: The reference wrong_tactic was not found.\n")
            self.checked.append(gid)
            out[gid] = verdict
        return out

    def falsify(self, where, out, run):
        out.mkdir(parents=True, exist_ok=True)
        (out / "FALSIFY.json").write_text(json.dumps(dict(verdict="passed")))
        self.falsified.append(where.gid)
        return dict(verdict="passed")

    repack_size = 20000

    def repackage(self, run, function, where, tier, bound, reason):
        out = where.d / "package" / where.gid
        out.mkdir(parents=True, exist_ok=True)
        (out / ("TASK-%s.md" % tier)).write_text("r" * self.repack_size)
        record = dict(next="prover", prompt_bound=bound, bound_reason=reason, **{"class": None})
        (out / "PACKAGE.json").write_text(json.dumps(record))
        self.repackaged = getattr(self, "repackaged", []) + [(where.gid, tier, bound)]
        return record

    def refute(self, where, text, out):
        return False


class FakeHandle:
    count = 0

    def __init__(self, prompt, reply):
        FakeHandle.count += 1
        self.id = "Fake%d" % FakeHandle.count
        self.prompt, self.reply = prompt, reply

    def done(self):
        return True


class FakeAgents:
    """agent/wait/tool helpers of the kernel. An agent spawned with tools calls its one tool with each proof
    USE_TOOL(prompt) lists, before it replies; the answers go to tool_results[label]."""

    def __init__(self, reply, use_tool=None):
        self.reply, self.spawned, self.writes = reply, [], []
        self.use_tool, self.tool_results, self.tools_of = use_tool, {}, {}
        agents = self

        class Tool:
            def __init__(self):
                self.defined, self.undefined = {}, []

            def __call__(self, fn, name=None, description=None):
                self.defined[name or fn.__name__] = fn
                return fn

            def undefine(self, name):
                self.undefined.append(name)
                del self.defined[name]

            async def write(self, args):
                agents.writes.append(args)
        self.tool = Tool()

    def agent(self, prompt, agent=None, label=None, schema=None, tools=None):
        self.tools_of[label] = list(tools or [])
        if tools and self.use_tool:
            self.tool_results[label] = [self.tool.defined[tools[0]](proof) for proof in self.use_tool(prompt)]
        handle = FakeHandle(prompt, self.reply(prompt) if callable(self.reply) else self.reply)
        self.spawned.append((agent, label, handle))
        return handle

    def wait(self, handles, raise_errors=True):
        return [h.reply for h in handles]


class CheckTextTests(unittest.TestCase):
    """The text check_proof returns: the cut before the failing sentence, the goals Show printed, the clip."""
    HEAD = "Lemma l : forall x : Z, x <= x.\nProof.\n"

    def test_show_text_cuts_before_the_failing_sentence_keeping_its_bullet(self):
        proof_v = self.HEAD + "intros x. destruct x.\n- lia.\n- wrong_tactic; lia.\n- lia.\nQed.\n"
        log = 'File "./proof.v", line 5, characters 2-14:\nError: The reference wrong_tactic was not found.'
        self.assertEqual(drive.show_text(proof_v, log, self.HEAD),
                         self.HEAD + "intros x. destruct x.\n- lia.\n-\nShow.\nAbort.\n")
        # An error at Qed shows the goals left; an error outside the proof shows nothing.
        qed = 'File "./proof.v", line 7, characters 0-4:\nError:  (in proof l): Attempt to save an incomplete proof'
        self.assertTrue(drive.show_text(proof_v, qed, self.HEAD).endswith("- lia.\nShow.\nAbort.\n"))
        self.assertIsNone(drive.show_text(proof_v, 'File "./proof.v", line 1, characters 0-5:\nError: x', self.HEAD))
        self.assertIsNone(drive.show_text(proof_v, "Error: no location", self.HEAD))

    def test_shown_goals_and_error_clip(self):
        log = "0.1 Warning: x\n0.2 1 goal\n0.2   \n0.2   x : Z\n0.2   ============================\n0.2   x <= x\n" \
              "0.3 @@CPU user=1 sys=0 maxrss_kib=5"
        self.assertEqual(drive.shown_goals(log), "1 goal\n  \n  x : Z\n  ============================\n  x <= x")
        state = "1 goal\n" + "".join("  h%d : Z\n" % i for i in range(400)) + "  =====\n  conclusion_here"
        text = drive.error_text("Error: boom", state, 1500)
        self.assertLessEqual(len(text.encode()), 1500)
        self.assertTrue(text.startswith("Error: boom" + drive.STATE_HEAD + drive.STATE_CUT))
        self.assertTrue(text.endswith("conclusion_here"))
        self.assertEqual(drive.error_text("e" * 3000, "", 1500), drive.clip("e" * 3000, 1500))

    def test_check_parallel_from_memory(self):
        self.assertEqual(drive.check_parallel(10 * drive.CHECK_PEAK_BYTES), 7)
        self.assertEqual(drive.check_parallel(0), 1)


class DriveTests(unittest.TestCase):
    def setUp(self):
        self.tmp = tempfile.TemporaryDirectory()
        self.run_dir = Path(self.tmp.name) / "run"
        make_meaning(self.run_dir, [("lemA", [], "forall x : Z, x <= x"),
                                    ("lemB", ["lemA"], "forall y : Z, y + 0 = y"),
                                    ("lemC", ["lemA", "lemB"], "forall z : Z, z * 1 = z")])
        self.kernel = FakeKernel()
        self.saved = dispatch_kernel.usage
        dispatch_kernel.usage = lambda agent_id: dict(tokens_in=1200, tokens_out=80,
                                                      resolved_model="anthropic/claude-haiku-5-5:low")
        dispatch_kernel._STATE.update(overrides={"scout": "base"}, live=[], current={})
        self.saved_compile = drive.probe_compile
        self.compiled = []
        drive.probe_compile = self.fake_compile
        self.install(GOOD)

    def tearDown(self):
        dispatch_kernel.usage = self.saved
        drive.probe_compile = self.saved_compile
        for name in ("agent", "wait", "tool"):
            drive_kernel.__dict__.pop(name, None)
        self.tmp.cleanup()

    def fake_compile(self, where, out, proof):
        """drive.probe_compile without Rocq: writes its scratch files, passes a proof using `lia`."""
        out.mkdir(parents=True, exist_ok=True)
        (out / "proof.v").write_text(proof)
        (out / "check.log").write_text("log")
        self.compiled.append((where.gid, out, proof))
        if "lia." in proof:
            return True, ""
        return False, ("File \"./proof.v\", line 9, characters 8-19:\nError: The reference wrong_tactic was not found.",
                       "1 goal\n  \n  x : Z\n  ============================\n  x <= x")

    def install(self, reply, use_tool=None):
        self.agents = FakeAgents(reply, use_tool)
        drive_kernel.agent, drive_kernel.wait, drive_kernel.tool = self.agents.agent, self.agents.wait, self.agents.tool

    def state(self):
        return store.fold(store.read_events(self.run_dir))

    def sid(self, name):
        return store.meaning_id(F, name)

    def test_round_closes_goal_and_records_tokens(self):
        summary = drive_kernel.run_round(F, self.run_dir, tier="haiku-low", kernel=self.kernel)
        # step before the round: falsify, then mechanical (fails), so lemA reaches haiku-low.
        self.assertEqual(summary["step_before"].get("mechanical"), 1)
        self.assertEqual(summary["started"], 1)
        self.assertEqual(summary["verdicts"], {"proved": 1})
        self.assertEqual([a for a, _, _ in self.agents.spawned], ["sonic"])
        prompt = self.agents.spawned[0][2].prompt
        self.assertTrue(prompt.startswith(drive.WITH_CHECK))
        self.assertEqual(drive.preamble("haiku-low"), drive.WITH_CHECK)
        self.assertIn("## Answer form", prompt)
        item = self.state()[self.sid("lemA")]
        self.assertEqual((item["state"], item["closed_by"]), ("closed", "haiku-low"))
        closed = item["events"][-1]
        self.assertEqual((closed["tokens_in"], closed["tokens_out"], closed["attempt"]), (1200, 80, 1))
        self.assertEqual((closed["prompt_sha256"], closed["answer_bytes"]), (drive.sha(prompt), len(GOOD)))
        self.assertTrue(closed["artifact"]["path"].endswith("goals/lemA/proof.v"))
        running = [e for e in item["events"] if e["state"] == "running" and e["tier"] == "haiku-low"]
        self.assertEqual(len(running), 1)
        where = drive.locate(self.run_dir, F)[self.sid("lemA")]
        meta = json.loads(where.answer_json.read_text())
        self.assertEqual((meta["resolved_model"], meta["agent_id"]), ("anthropic/claude-haiku-5-5:low",
                                                                      self.agents.spawned[0][2].id))
        self.assertEqual(where.prompt_path("haiku-low", 1).read_text(), prompt)
        # The step after the round unblocked lemB (its only dependency closed) and ran it to haiku-low.
        self.assertEqual(summary["step_after"].get("unblocked"), 1)
        self.assertEqual(summary["next_model"], {"haiku-low": 1})

    def test_check_tool_budget_and_accounting(self):
        wrong = "intros. wrong_tactic.\nQed."
        self.install(GOOD, use_tool=lambda prompt: [wrong] * 4 + ["intros. lia.\nQed."] * 4)
        summary = drive_kernel.run_round(F, self.run_dir, tier="haiku-low", kernel=self.kernel)
        label = self.agents.spawned[0][1]
        results = self.agents.tool_results[label]
        # Six calls compile (the budget of tiers.json), the rest are refused without a compile.
        self.assertEqual(len(self.compiled), 6)
        self.assertEqual([r["remaining"] for r in results], [5, 4, 3, 2, 1, 0, 0, 0])
        self.assertEqual([r["ok"] for r in results], [False] * 4 + [True] * 2 + [False] * 2)
        self.assertIn("No check_proof calls left", results[-1]["error"])
        self.assertIn("wrong_tactic was not found", results[0]["error"])
        self.assertIn("Goal state before the failing sentence", results[0]["error"])
        self.assertLessEqual(max(len(r["error"].encode()) for r in results), drive.CHECK_ERROR_BYTES)
        # The tool was given to that agent only, and undefined after the batch.
        tool_name = self.agents.tools_of[label][0]
        self.assertTrue(tool_name.startswith("check_proof_"))
        self.assertEqual((self.agents.tool.defined, self.agents.tool.undefined), ({}, [tool_name]))
        # Accounting: the answer record and the result event carry the six calls; the kernel check
        # still decided the attempt.
        self.assertEqual(summary["check_calls"], 6)
        item = self.state()[self.sid("lemA")]
        closed = item["events"][-1]
        self.assertEqual(closed["state"], "closed")
        self.assertEqual(closed["context_items"], ["task", "check_calls:6"])
        self.assertIn(self.sid("lemA").rsplit("/", 1)[-1], self.kernel.checked)
        where = drive.locate(self.run_dir, F)[self.sid("lemA")]
        self.assertEqual(json.loads(where.answer_json.read_text())["check_calls"], 6)
        lines = dict(report.measures(self.run_dir, F))
        self.assertEqual(lines["check tool haiku-low"], "attempts 1 with the tool (0 without), check calls per "
                         "closed goal 6.0, tokens per attempt with the tool 1280.0, without n/a")

    def test_check_tool_is_bound_to_its_goal(self):
        run = Path(self.tmp.name) / "two"
        make_meaning(run, [("lemX", [], "forall x : Z, x <= x"), ("lemY", [], "forall y : Z, y <= y")])
        self.install(GIVE_UP, use_tool=lambda prompt: ["intros. lia.\nQed."])
        drive_kernel.run_round(F, run, tier="haiku-low", kernel=self.kernel)
        self.assertEqual(sorted(gid for gid, _, _ in self.compiled), ["lemX", "lemY"])
        for gid, out, _ in self.compiled:
            self.assertEqual(out, run / "meaning" / gid / "probes" / gid / "haiku-low-1" / "1")
        names = [tools[0] for tools in self.agents.tools_of.values()]
        self.assertEqual(len(set(names)), 2)
        # Each tool's calls reached its own goal: the agent of lemX compiled lemX.
        for (_, label, handle) in self.agents.spawned:
            gid = "lemX" if "lemX" in label else "lemY"
            self.assertIn("Lemma %s" % gid, open(run / "meaning" / gid / "goals" / gid / "goal.v").read())
            self.assertIn(gid, handle.prompt)
        state = store.fold(store.read_events(run))
        self.assertEqual({state[store.meaning_id(F, g)]["events"][-1]["context_items"][-1] for g in ("lemX", "lemY")},
                         {"check_calls:1"})

    def test_tool_calls_leave_store_and_answers_untouched(self):
        drive.step(F, self.run_dir, kernel=self.kernel)
        identifier = self.sid("lemA")
        prompt, items = drive.prompt_for(self.run_dir, F, identifier, "haiku-low")
        attempt = drive.register_attempt(self.run_dir, F, identifier, "haiku-low", prompt, items)
        where = drive.locate(self.run_dir, F)[identifier]

        def snapshot():
            return {str(p.relative_to(self.run_dir)): p.read_bytes() for p in self.run_dir.rglob("*")
                    if p.is_file() and "probes" not in p.parts}
        before = snapshot()
        probe = drive.ProofProbe(where, "haiku-low", attempt, calls=3)
        self.assertFalse(probe("intros. wrong_tactic.\nQed.")["ok"])
        self.assertTrue(probe("intros. lia.\nQed.")["ok"])
        self.assertEqual(probe("intros. lia.")["error"], "the answer must end with exactly one Qed.")
        self.assertEqual(probe("intros. lia.\nQed.")["remaining"], 0)
        self.assertEqual((probe.calls, len(self.compiled)), (3, 2))
        self.assertEqual(snapshot(), before)
        self.assertTrue((where.d / "probes" / "lemA" / "haiku-low-1" / "2" / "proof.v").is_file())

    def test_tier_without_check_tool_gets_no_tool(self):
        saved = drive.check_tool
        drive.check_tool = lambda tier: (False, 0)
        try:
            drive_kernel.run_round(F, self.run_dir, tier="haiku-low", kernel=self.kernel)
        finally:
            drive.check_tool = saved
        label = self.agents.spawned[0][1]
        self.assertEqual(self.agents.tools_of[label], [])
        self.assertTrue(self.agents.spawned[0][2].prompt.startswith(drive.NO_TOOLS))
        self.assertIsNone(self.state()[self.sid("lemA")]["events"][-1]["context_items"])

    def test_reopen_resets_a_failed_goal_and_only_limits_the_round(self):
        self.install(BAD)
        drive_kernel.run_round(F, self.run_dir, tier="haiku-low", kernel=self.kernel)
        self.assertEqual(self.state()[self.sid("lemA")]["state"], "failed")
        self.assertEqual(drive.reopen(F, self.run_dir, [self.sid("lemA"), self.sid("lemB")]), [self.sid("lemA")])
        item = self.state()[self.sid("lemA")]
        self.assertEqual((item["state"], item["resets"]), ("derived", 1))
        summary = drive_kernel.run_round(F, self.run_dir, tier="haiku-low", kernel=self.kernel,
                                         only=[self.sid("lemB")])
        self.assertEqual(summary["started"], 0)
        summary = drive_kernel.run_round(F, self.run_dir, tier="haiku-low", kernel=self.kernel,
                                         only=[self.sid("lemA")])
        self.assertEqual(summary["started"], 1)

    def test_repeated_prompt_is_refused(self):
        drive.step(F, self.run_dir, kernel=self.kernel)
        prompt, items = drive.prompt_for(self.run_dir, F, self.sid("lemA"), "haiku-low")
        drive.register_attempt(self.run_dir, F, self.sid("lemA"), "haiku-low", prompt, items)
        drive.answer(self.run_dir, F, self.sid("lemA"), "haiku-low", 1, prompt, GIVE_UP)
        with self.assertRaises(store.Rejected):
            drive.register_attempt(self.run_dir, F, self.sid("lemA"), "haiku-low", prompt, items)

    def test_compile_error_changes_the_retry_prompt(self):
        self.install(BAD)
        drive_kernel.run_round(F, self.run_dir, tier="haiku-low", kernel=self.kernel)
        item = self.state()[self.sid("lemA")]
        self.assertEqual((item["state"], item["failure"]), ("failed", "compile_error"))
        first = self.agents.spawned[0][2].prompt
        self.install(GOOD)
        summary = drive_kernel.run_round(F, self.run_dir, tier="haiku-low", kernel=self.kernel)
        self.assertEqual(summary["started"], 1)
        second = self.agents.spawned[0][2].prompt
        self.assertNotEqual(drive.sha(first), drive.sha(second))
        self.assertTrue(second.startswith(first))
        self.assertIn("wrong_tactic was not found", second)
        self.assertIn("intros. wrong_tactic.", second)
        item = self.state()[self.sid("lemA")]
        self.assertEqual((item["state"], item["tier_attempts"]["haiku-low"]), ("closed", 2))

    def test_closing_a_blocker_unblocks_dependants(self):
        drive.step(F, self.run_dir, kernel=self.kernel)
        self.assertEqual(self.state()[self.sid("lemC")]["blocked_by"], self.sid("lemA"))
        drive_kernel.run_round(F, self.run_dir, tier="haiku-low", kernel=self.kernel)
        state = self.state()
        self.assertEqual(state[self.sid("lemA")]["state"], "closed")
        self.assertEqual((state[self.sid("lemC")]["state"], state[self.sid("lemC")]["blocked_by"]),
                         ("blocked-on", self.sid("lemB")))
        self.assertEqual(state[self.sid("lemB")]["state"], "failed")  # mechanical tried, haiku-low next
        drive_kernel.run_round(F, self.run_dir, tier="haiku-low", kernel=self.kernel)
        state = self.state()
        self.assertEqual(state[self.sid("lemB")]["state"], "closed")
        lem_c = state[self.sid("lemC")]
        derived = [e for e in lem_c["events"] if e["state"] == "derived" and e["tier"] == "falsify"]
        self.assertEqual(len(derived), 1)  # the falsity verdict carried, goal.v unchanged
        self.assertEqual(self.kernel.falsified.count("lemC"), 1)
        self.assertEqual(drive.model_items(self.run_dir, F), [(self.sid("lemC"), "haiku-low",
                                                               "first attempt at this tier")])

    def test_scout_tier_needs_its_override(self):
        # routing.json's ladder: haiku-low 2, haiku-medium 0 (off), haiku-high 1, opus-medium 2.
        self.install(GIVE_UP)
        drive_kernel.run_round(F, self.run_dir, tier="haiku-low", kernel=self.kernel)
        self.assertEqual([t for _, t, _ in drive.model_items(self.run_dir, F)], ["haiku-high"])
        with self.assertRaises(drive_kernel.DriveError):
            drive_kernel.run_round(F, self.run_dir, tier="haiku-high", kernel=self.kernel)
        summary = drive_kernel.run_round(F, self.run_dir, kernel=self.kernel)
        self.assertEqual((summary["started"], list(summary["skipped"])), (0, ["haiku-high"]))
        asyncio.run(drive_kernel.set_tier_override("haiku-high"))
        self.assertEqual(json.loads(self.agents.writes[-1]["content"])["scout"], "anthropic/claude-haiku-5-5:high")
        self.install(GOOD)
        summary = drive_kernel.run_round(F, self.run_dir, tier="haiku-high", kernel=self.kernel)
        self.assertEqual(summary["started"], 1)
        self.assertEqual(self.agents.spawned[0][0], "scout")
        self.assertEqual(self.state()[self.sid("lemA")]["closed_by"], "haiku-high")

    def test_spawn_asks_for_the_answer_schema(self):
        captured = []
        agents = FakeAgents(GOOD)
        drive_kernel.agent = lambda prompt, agent=None, label=None, schema=None, **options: (
            captured.append(schema) or agents.agent(prompt, agent, label, **options))
        drive_kernel.run_round(F, self.run_dir, tier="haiku-low", kernel=self.kernel)
        self.assertEqual(captured[0]["required"], ["verdict"])

    def test_need_context_without_supply_escalates_without_spending(self):
        self.install(json.dumps(dict(verdict="need_context", needs=["nothing_known_here"])))
        drive_kernel.run_round(F, self.run_dir, tier="haiku-low", kernel=self.kernel)
        item = self.state()[self.sid("lemA")]
        self.assertEqual((item["state"], item["failure"], item["tier_attempts"]["haiku-low"]),
                         ("failed", "missing_context", 1))
        self.assertEqual([t for _, t, _ in drive.model_items(self.run_dir, F)], ["haiku-high"])
        self.assertEqual(drive_kernel.resolve_needs(["nothing_known_here"], drive.locate(self.run_dir, F)[
            self.sid("lemA")].goal_dir), "")

    def test_need_context_with_a_named_goal_retries_the_tier(self):
        self.install(json.dumps(dict(verdict="need_context", needs=["lemB_statement"])))
        drive_kernel.run_round(F, self.run_dir, tier="haiku-low", kernel=self.kernel)
        self.assertEqual(drive.model_items(self.run_dir, F)[0][:2], (self.sid("lemA"), "haiku-low"))
        prompt, items = drive.prompt_for(self.run_dir, F, self.sid("lemA"), "haiku-low")
        self.assertIn("forall y : Z, y + 0 = y", prompt)
        self.assertIn("context:lemB", items)

    def test_reset_marks_the_repeated_mechanical_prompt_and_reruns_the_ladder(self):
        drive.step(F, self.run_dir, kernel=self.kernel)
        self.install(GIVE_UP)
        drive_kernel.run_round(F, self.run_dir, tier="haiku-low", kernel=self.kernel)
        item = self.state()[self.sid("lemA")]
        store.append(self.run_dir, store.event(id=item["id"], function=F, kind="meaning", state="derived",
                                               artifact=item["artifact"]))
        counts = drive.step(F, self.run_dir, kernel=self.kernel)[0]
        self.assertEqual(counts.get("repeated_prompt"), 1)
        self.assertEqual(drive.model_items(self.run_dir, F)[0][:2], (self.sid("lemA"), "haiku-low"))

    def test_malformed_reply_retries_with_a_changed_prompt(self):
        self.install("I could not decide.")
        drive_kernel.run_round(F, self.run_dir, tier="haiku-low", kernel=self.kernel)
        first = self.agents.spawned[0][2].prompt
        self.assertEqual(self.state()[self.sid("lemA")]["failure"], "malformed")
        summary = drive_kernel.run_round(F, self.run_dir, tier="haiku-low", kernel=self.kernel)
        second = self.agents.spawned[-1][2].prompt
        self.assertEqual(summary["started"], 1)
        self.assertEqual(second, drive.MALFORMED_LINE + first)
        # A second malformed reply counts: the tier has one proof attempt left by count, but the goal moves on.
        self.assertEqual([t for _, t, _ in drive.model_items(self.run_dir, F)], ["haiku-high"])


class GoalLocationTests(unittest.TestCase):
    def test_block_goal_is_located_and_prompted_with_its_source(self):
        with tempfile.TemporaryDirectory() as tmp:
            run = Path(tmp)
            d = run / "residual" / "00c4"
            statement = "forall a : Z, 0 <= a -> 0 <= a + 1"
            (d / "goals" / "00c4-1").mkdir(parents=True)
            (d / "goals" / "00c4-1" / "goal.v").write_text(goal_v("residual_fn_00c4_x", statement))
            (d / "tasks").mkdir()
            (d / "tasks" / "00c4-1.md").write_text("# Residual goal 00c4-1\n\nThe exact source is in goal.v.\n")
            (d / "MANIFEST.json").write_text(json.dumps(dict(block="00c4", bank="/nonexistent", goals=[
                dict(id="00c4-1", name="residual_fn_00c4_x", statement=statement, reparse="exact")])))
            identifier = store.goal_id(F, "00c4", statement)
            located = drive.locate(run, F)
            self.assertEqual(list(located), [identifier])
            store.append(run, store.event(id=identifier, function=F, kind="goal", state="derived"))
            prompt, items = drive.prompt_for(run, F, identifier, "haiku-low")
            self.assertIn(drive.EXACT_HEADING, prompt)
            self.assertIn("0 <= a + 1", prompt)
            self.assertIn("## Answer form", prompt)
            self.assertEqual(items, ["task"])


class PackagedGoalTests(unittest.TestCase):
    """A block goal with a package.py task, the prompt bound and the too_large escalation."""

    def setUp(self):
        self.tmp = tempfile.TemporaryDirectory()
        self.run = Path(self.tmp.name)
        self.d = self.run / "resid" / "0058"
        statement = "forall a : Z, 0 <= a -> 0 <= a + 1"
        (self.d / "goals" / "0058-1").mkdir(parents=True)
        # The residual goal is huge (its exact source), the package task is bounded.
        (self.d / "goals" / "0058-1" / "goal.v").write_text(goal_v("residual_fn_0058_x", statement + " " * 40000))
        (self.d / "tasks").mkdir()
        (self.d / "tasks" / "0058-1.md").write_text("# Residual goal 0058-1\n" + "x" * 30000)
        self.package = self.d / "package" / "0058-1"
        self.package.mkdir(parents=True)
        (self.d / "MANIFEST.json").write_text(json.dumps(dict(block="0058", bank="/nonexistent", goals=[
            dict(id="0058-1", name="residual_fn_0058_x", statement=statement, reparse="exact")])))
        self.identifier = store.goal_id(F, "0058", statement)
        store.append(self.run, [store.event(id=self.identifier, function=F, kind="goal", state="derived"),
                                store.event(id=self.identifier, function=F, kind="goal", state="derived",
                                            tier="falsify")])
        self.kernel = FakeKernel()
        self.saved = drive.replay.load_routing

    def tearDown(self):
        drive.replay.load_routing = self.saved
        self.tmp.cleanup()

    def test_package_task_is_the_prompt(self):
        (self.package / "TASK-haiku-low.md").write_text("# Packaged goal\n\n" + package_answer_form())
        prompt, items = drive.prompt_for(self.run, F, self.identifier, "haiku-low")
        self.assertEqual(prompt, drive.WITH_CHECK + "# Packaged goal\n\n" + package_answer_form())
        self.assertNotIn(drive.EXACT_HEADING, prompt)
        # Another tier falls back to the tier-less package task.
        (self.package / "TASK.md").write_text("# Tier-less\n")
        prompt, _ = drive.prompt_for(self.run, F, self.identifier, "haiku-high")
        self.assertTrue(prompt.startswith(drive.WITH_CHECK + "# Tier-less\n"))

    def test_class_bound_of_routing_json_capped_by_the_tier(self):
        drive.replay.load_routing = lambda: {"classes": {"BIG": {"max_prompt_bytes": 50000}}}
        self.assertEqual(drive.max_prompt_bytes("haiku-low", "BIG"), 32000)
        self.assertEqual(drive.max_prompt_bytes("haiku-low", None), 12000)

    def test_large_goal_is_repackaged_once_at_the_tier_cap(self):
        (self.package / "TASK-haiku-low.md").write_text("y" * 20000)
        counts = drive.step(F, self.run, kernel=self.kernel)[0]
        self.assertEqual(counts.get("repackaged_large"), 1)
        self.assertEqual(self.kernel.repackaged, [("0058-1", "haiku-low", 32000)])
        self.assertEqual([t for _, t, _ in drive.model_items(self.run, F)], ["haiku-low"])
        prompt, items = drive.prompt_for(self.run, F, self.identifier, "haiku-low")
        self.assertGreater(len(prompt.encode()), 12000)
        self.assertIn("prompt_bound:32000", items)
        record = json.loads((self.package / "PACKAGE.json").read_text())
        self.assertTrue(record["bound_reason"].startswith("smallest task over the default bound"))
        # The attempt carries the bound for report.py.
        drive.register_attempt(self.run, F, self.identifier, "haiku-low", prompt, items)
        running = store.fold(store.read_events(self.run))[self.identifier]["events"][-1]
        self.assertIn("prompt_bound:32000", running["context_items"])

    def test_goal_too_large_at_the_cap_waits_for_a_decision(self):
        (self.package / "TASK-haiku-low.md").write_text("y" * 20000)
        self.kernel.repack_size = 40000
        counts = drive.step(F, self.run, kernel=self.kernel)[0]
        self.assertEqual((counts.get("repackaged_large"), counts.get("waiting_decision_too_large")), (1, 1))
        item = store.fold(store.read_events(self.run))[self.identifier]
        self.assertEqual(item["state"], "waiting-decision")
        reasons = json.loads(Path(item["artifact"]["path"]).read_text())
        self.assertEqual(set(reasons), {"haiku-low", "haiku-high", "opus-medium"})
        self.assertTrue(all(r.startswith("too-large: ") and r.endswith("> 32000 bytes") for r in reasons.values()))
        self.assertEqual(drive.model_items(self.run, F), [])

    def test_package_class_address_goes_to_the_owner(self):
        (self.package / "PACKAGE.json").write_text(json.dumps(dict(id=self.identifier, **{"class": "ADDRESS"},
                                                                 next="decision")))
        counts = drive.step(F, self.run, kernel=self.kernel)[0]
        self.assertEqual(counts.get("address"), 1)
        self.assertEqual(drive.model_items(self.run, F), [])
        self.assertEqual([a for i, a, _, _ in drive.route.next_items(self.run, F)], ["owner"])

    def test_symbolized_package_returns_an_address_goal_to_the_ladder(self):
        store.append(self.run, store.event(id=self.identifier, function=F, kind="goal", state="derived",
                                           **{"class": "ADDRESS"}))
        self.assertEqual([a for _, a, _, _ in drive.route.next_items(self.run, F)], ["owner"])
        (self.package / "PACKAGE.json").write_text(json.dumps(dict(id=self.identifier, symbols=[dict(
            literal="lit", notation="sym_x")], **{"class": None})))
        (self.package / "TASK-haiku-low.md").write_text("# Symbolized goal\n")
        counts = drive.step(F, self.run, kernel=self.kernel)[0]
        self.assertEqual(counts.get("symbolized"), 1)
        item = store.fold(store.read_events(self.run))[self.identifier]
        self.assertEqual(item["goal_class"], drive.replay.goal_class("forall a : Z, 0 <= a -> 0 <= a + 1"))
        self.assertEqual([t for _, t, _ in drive.model_items(self.run, F)], ["haiku-low"])


def package_answer_form():
    return drive.package.ANSWER_FORM.format(answer="answers/0058-1.v")


if __name__ == "__main__":
    unittest.main()
