"""Production driver with a fake agent and a fake kernel (no model, no Rocq): one round closes a goal and
records its events and tokens, a repeated prompt is refused, a compile error gives a changed retry
prompt, closing a blocker unblocks its dependants, and the Haiku tiers' per-call model on rocq-prover."""
import json
from pathlib import Path
import sys
import tempfile
import unittest

HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE))
import dispatch_kernel  # noqa: E402
import drive  # noqa: E402
import defs  # noqa: E402
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


def legacy_rows(rows_of, **overrides):
    """drive.tier_rows of tiers.json with the model tiers as before lookup, check_counterexample and
    best-of-N (check_proof at 6 calls, one sample), then OVERRIDES per tier name ({tier: {key: value}})."""
    def rows(path=None):
        out = {name: dict(row) for name, row in rows_of().items()}
        for row in out.values():
            if row.get("agent"):
                row.update(check_calls=6, lookup_calls=0, counterexample_calls=0, samples=1)
        for name, values in overrides.items():
            out[name].update(values)
        return out
    return rows


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
        record = dict(next="prover", prompt_bound=bound, reserve=drive.package_reserve(tier), bound_reason=reason,
                      **{"class": None})
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
    """agent/wait/tool helpers of the kernel. An agent spawned with tools calls its first tool (check_proof)
    with each proof USE_TOOL(prompt) lists, before it replies; the answers go to tool_results[label].
    SCRIPT(prompt, tools), when given, is called instead with {tool kind: function} (`check_proof`,
    `lookup`, `search`, `check_counterexample`) and its return value goes to tool_results[label]."""

    def __init__(self, reply, use_tool=None, script=None):
        self.reply, self.spawned, self.models = reply, [], {}
        self.use_tool, self.script, self.tool_results, self.tools_of = use_tool, script, {}, {}
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
        self.tool = Tool()

    def agent(self, prompt, agent=None, label=None, schema=None, tools=None, model=None):
        self.models[label] = model
        self.tools_of[label] = list(tools or [])
        if tools and self.script:
            kinds = {name.rsplit("_", 1)[0]: self.tool.defined[name] for name in tools}
            self.tool_results[label] = self.script(prompt, kinds)
        elif tools and self.use_tool:
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


class DriveBase(unittest.TestCase):
    """The run dir of three meaning goals (lemA, lemB on lemA, lemC on both), a fake kernel, fake
    agents and the tiers of tiers.json as before the lookup and counterexample tools and best-of-N
    (legacy_rows)."""

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
        dispatch_kernel._STATE.update(live=[])
        self.saved_compile = drive.probe_compile
        self.compiled = []
        drive.probe_compile = self.fake_compile
        self.install(GOOD)
        self.saved_rows = drive.tier_rows
        drive.tier_rows = legacy_rows(self.saved_rows)

    def tearDown(self):
        dispatch_kernel.usage = self.saved
        drive.probe_compile = self.saved_compile
        drive.tier_rows = self.saved_rows
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

    def install(self, reply, use_tool=None, script=None):
        self.agents = FakeAgents(reply, use_tool, script)
        drive_kernel.agent, drive_kernel.wait, drive_kernel.tool = self.agents.agent, self.agents.wait, self.agents.tool

    def state(self):
        return store.fold(store.read_events(self.run_dir))

    def sid(self, name):
        return store.meaning_id(F, name)


class DriveTests(DriveBase):
    def test_round_closes_goal_and_records_tokens(self):
        summary = drive_kernel.run_round(F, self.run_dir, tier="haiku-low", kernel=self.kernel)
        # step before the round: falsify, then mechanical (fails), so lemA reaches haiku-low.
        self.assertEqual(summary["step_before"].get("mechanical"), 1)
        self.assertEqual(summary["started"], 1)
        self.assertEqual(summary["verdicts"], {"proved": 1})
        self.assertEqual([a for a, _, _ in self.agents.spawned], ["rocq-prover"])
        self.assertEqual(self.agents.models[self.agents.spawned[0][1]], "anthropic/claude-haiku-5-5:low")
        prompt = self.agents.spawned[0][2].prompt
        self.assertTrue(prompt.startswith(drive.preamble("haiku-low")))
        self.assertTrue(drive.preamble("haiku-low").startswith(drive.TOOLS_HEAD))
        self.assertIn("check_proof(proof)", drive.preamble("haiku-low"))
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

    def test_haiku_high_runs_rocq_prover_at_its_per_call_model(self):
        # routing.json's ladder: haiku-low 2, haiku-medium 0 (off), haiku-high 1, opus-medium 2.
        self.install(GIVE_UP)
        drive_kernel.run_round(F, self.run_dir, tier="haiku-low", kernel=self.kernel)
        self.assertEqual([t for _, t, _ in drive.model_items(self.run_dir, F)], ["haiku-high"])
        self.install(GOOD)
        summary = drive_kernel.run_round(F, self.run_dir, kernel=self.kernel)
        self.assertEqual((summary["started"], summary["skipped"]), (1, {}))
        agent, label, _ = self.agents.spawned[0]
        self.assertEqual((agent, self.agents.models[label]), ("rocq-prover", "anthropic/claude-haiku-5-5:high"))
        self.assertEqual(self.state()[self.sid("lemA")]["closed_by"], "haiku-high")

    def test_opus_tier_passes_no_model(self):
        self.assertEqual(dispatch_kernel.spawn_options(drive.tier_rows()["opus-medium"]), dict(agent="task"))

    def test_spawn_asks_for_the_answer_schema(self):
        captured = []
        agents = FakeAgents(GOOD)
        drive_kernel.agent = lambda prompt, agent=None, label=None, schema=None, **options: (
            captured.append(schema) or agents.agent(prompt, agent, label, **options))
        drive_kernel.run_round(F, self.run_dir, tier="haiku-low", kernel=self.kernel)
        self.assertEqual(captured[0]["required"], ["verdict"])

    def test_reset_drops_feedback_it_cannot_build_instead_of_escalating(self):
        self.install(json.dumps(dict(verdict="need_context", needs=["nothing_known_here"])))
        drive_kernel.run_round(F, self.run_dir, tier="haiku-low", kernel=self.kernel)
        self.assertEqual(self.state()[self.sid("lemA")]["failure"], "missing_context")
        first = self.agents.spawned[0][2].prompt
        self.assertEqual(drive.reopen(F, self.run_dir, [self.sid("lemA")]), [self.sid("lemA")])
        self.assertIsNone(drive.last_since_reset(self.state()[self.sid("lemA")]))
        prompt, items = drive.prompt_for(self.run_dir, F, self.sid("lemA"), "haiku-low")
        self.assertEqual((prompt, items), (first, ["task"]))

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
        self.assertEqual(prompt, drive.preamble("haiku-low") + "# Packaged goal\n\n" + package_answer_form())
        self.assertNotIn(drive.EXACT_HEADING, prompt)
        # Another tier falls back to the tier-less package task.
        (self.package / "TASK.md").write_text("# Tier-less\n")
        prompt, _ = drive.prompt_for(self.run, F, self.identifier, "haiku-high")
        self.assertTrue(prompt.startswith(drive.preamble("haiku-high") + "# Tier-less\n"))

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

    def test_package_cut_for_a_shorter_preamble_is_repackaged_once_more(self):
        # A package at the cap from before the tool preamble (no `reserve`) leaves no room for it.
        (self.package / "TASK-haiku-low.md").write_text("y" * 31800)
        (self.package / "PACKAGE.json").write_text(json.dumps(dict(next="prover", prompt_bound=32000, **{"class": None})))
        where = drive.locate(self.run, F)[self.identifier]
        self.assertTrue(drive.short_reserve(where, "haiku-low"))
        self.assertIsNone(drive.prompt_for(self.run, F, self.identifier, "haiku-low", sample=(2, 3))[0])
        self.kernel.repack_size = 32000 - drive.package_reserve("haiku-low") - 2000
        counts = drive.step(F, self.run, kernel=self.kernel)[0]
        self.assertEqual(counts.get("repackaged_large"), 1)
        self.assertFalse(drive.short_reserve(where, "haiku-low"))
        prompt, _ = drive.prompt_for(self.run, F, self.identifier, "haiku-low", sample=(2, 3))
        self.assertLessEqual(len(prompt.encode()), 32000)

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


FALSE_X3 = json.dumps(dict(verdict="false", counterexample="x = 3"))


class ProverToolTests(DriveBase):
    """lookup/search (budget, caching), check_counterexample and the refusal of an unconfirmed `false`, and
    the per-attempt tool accounting; haiku-low with 2 lookup and 2 counterexample calls, one sample."""

    def setUp(self):
        super().setUp()
        drive.tier_rows = legacy_rows(self.saved_rows, **{"haiku-low": dict(lookup_calls=2, counterexample_calls=2)})
        self.saved_refutation = drive.Kernel.refutation
        self.refuted = []
        drive.Kernel.refutation = self.fake_refutation
        self.saved_defs = (defs.goal_resolver, defs.lookup_text, defs.search)
        self.looked = []
        defs.goal_resolver = lambda goal_dir: "resolver of %s" % Path(goal_dir).name
        defs.lookup_text = lambda resolver, name: self.looked.append((resolver, name)) or "Definition %s := 0." % name
        defs.search = lambda resolver, pattern: self.looked.append((resolver, pattern)) or "lemma : %s" % pattern
        self.binder_kind = "Z"

    def tearDown(self):
        drive.Kernel.refutation = self.saved_refutation
        defs.goal_resolver, defs.lookup_text, defs.search = self.saved_defs
        super().tearDown()

    def fake_refutation(self, where, text, out, binders=None):
        """Kernel.refutation without Rocq: one binder x of kind binder_kind; `x = 3` refutes."""
        self.refuted.append((where.gid, text, binders))
        binders = [dict(name="x", kind=self.binder_kind)]
        return drive.refutation_of(binders, text, lambda values: values.get("x") == 3)

    def where(self):
        drive.step(F, self.run_dir, kernel=self.kernel)
        return drive.locate(self.run_dir, F)[self.sid("lemA")]

    def test_lookup_budget_and_caching(self):
        where = self.where()
        asked = []
        probe = drive.LookupProbe(where, 2, lookup=lambda n: asked.append(n) or "D " + n + "x" * 5000,
                                  search=lambda p: asked.append(p) or "S " + p)
        first = probe.lookup("arrayListLength")
        self.assertEqual(first["remaining"], 1)
        self.assertLessEqual(len(first["text"].encode()), drive.LOOKUP_BYTES)
        self.assertTrue(first["text"].endswith(drive.TRUNCATED))
        # The same name again (any spacing) is answered from the attempt's cache and costs nothing.
        self.assertEqual(probe.lookup(" arrayListLength "), first)
        self.assertEqual(probe.search("(_ * 32)%Z"), dict(text="S (_ * 32)%Z", remaining=0))
        self.assertIn("No lookup or search calls left", probe.lookup("keysBlockList")["text"])
        self.assertEqual(probe.lookup("arrayListLength"), dict(text=first["text"], remaining=0))
        self.assertEqual(asked, ["arrayListLength", "(_ * 32)%Z"])
        self.assertEqual((probe.lookups, probe.searches), (1, 1))
        self.assertEqual(probe.lookup("")["text"], "Give one non-empty string.")

    def test_round_hands_out_every_tool_and_records_its_calls(self):
        def script(prompt, tools):
            return [tools["lookup"]("lemB_statement"), tools["lookup"]("lemB_statement"), tools["search"]("Z.le_refl"),
                    tools["check_proof"]("intros. lia.\nQed.")]
        self.install(GOOD, script=script)
        summary = drive_kernel.run_round(F, self.run_dir, tier="haiku-low", kernel=self.kernel)
        label = self.agents.spawned[0][1]
        self.assertEqual([name.rsplit("_", 1)[0] for name in self.agents.tools_of[label]],
                         ["check_proof", "lookup", "search", "check_counterexample"])
        self.assertEqual(self.agents.tool.defined, {})
        results = self.agents.tool_results[label]
        self.assertEqual([r["remaining"] for r in results[:3]], [1, 1, 0])
        self.assertEqual(self.looked, [("resolver of lemA", "lemB_statement"), ("resolver of lemA", "Z.le_refl")])
        prompt = self.agents.spawned[0][2].prompt
        for text in (drive.LOOKUP_RULE, drive.FALSE_RULE, "lookup(name)", "check_counterexample(assignment)"):
            self.assertIn(text, prompt)
        item = self.state()[self.sid("lemA")]
        self.assertEqual(item["state"], "closed")
        self.assertEqual(item["events"][-1]["context_items"],
                         ["task", "check_calls:1", "lookup_calls:1", "search_calls:1", "counterexample_calls:0"])
        self.assertEqual(summary["tool_calls"], dict(check_calls=1, lookup_calls=1, search_calls=1,
                                                     counterexample_calls=0))
        where = drive.locate(self.run_dir, F)[self.sid("lemA")]
        self.assertEqual(json.loads(where.answer_json.read_text())["lookup_calls"], 1)

    def test_false_is_refused_without_a_confirmed_counterexample(self):
        refuted = []
        self.kernel.refute = lambda where, text, out: refuted.append(text) or True
        self.install(FALSE_X3)
        summary = drive_kernel.run_round(F, self.run_dir, tier="haiku-low", kernel=self.kernel)
        self.assertEqual(summary["verdicts"], {drive.UNCONFIRMED_FALSE: 1})
        item = self.state()[self.sid("lemA")]
        self.assertEqual((item["state"], item["failure"]), ("failed", drive.UNCONFIRMED_FALSE))
        self.assertEqual(refuted, [])  # refused without a kernel call
        self.assertEqual(drive.route.attempt_results(item)["haiku-low"], [drive.UNCONFIRMED_FALSE])

    def test_false_with_a_confirmed_counterexample_goes_to_the_kernel(self):
        refuted = []
        self.kernel.refute = lambda where, text, out: refuted.append(text) or True

        def script(prompt, tools):
            return [tools["check_counterexample"]("x = 5"), tools["check_counterexample"](" x =  3 ")]
        self.install(json.dumps(dict(verdict="false", counterexample="x = 3")), script=script)
        drive_kernel.run_round(F, self.run_dir, tier="haiku-low", kernel=self.kernel)
        results = self.agents.tool_results[self.agents.spawned[0][1]]
        self.assertEqual([(r["confirmed"], r["remaining"]) for r in results], [(False, 1), (True, 0)])
        self.assertIn("lemma holds there", results[0]["reason"])
        # The probe kept the goal's binders after its first call.
        self.assertEqual([b for _, _, b in self.refuted], [None, [dict(name="x", kind="Z")]])
        self.assertEqual(refuted, ["x = 3"])
        self.assertEqual(self.state()[self.sid("lemA")]["state"], "false")

    def test_unsupported_binders_say_so_and_the_prompt_forbids_false(self):
        where = self.where()
        self.binder_kind = "other"
        probe = drive.CounterexampleProbe(where, "haiku-low", 1, 2)
        first = probe("x = 3")
        self.assertFalse(first["confirmed"])
        self.assertTrue(first["reason"].startswith("unsupported"))
        self.assertIn("answer false is not allowed", first["reason"])
        self.assertEqual(probe("x = 4"), dict(confirmed=False, reason=first["reason"], remaining=1))
        self.assertEqual((probe.calls, len(self.refuted)), (1, 1))
        self.assertFalse(probe.accepts("x = 3"))
        (where.goal_dir / "falsify").mkdir(exist_ok=True)
        (where.goal_dir / "falsify" / "FALSIFY.json").write_text(json.dumps(dict(verdict="unchecked")))
        prompt, _ = drive.prompt_for(self.run_dir, F, self.sid("lemA"), "haiku-low")
        self.assertIn(drive.UNCHECKED_RULE, prompt)
        self.assertNotIn(drive.FALSE_RULE, prompt)

    def test_counterexample_naming_no_variable_is_not_confirmed(self):
        confirmed, reason, _ = drive.refutation_of([dict(name="x", kind="Z")], "the list is empty", lambda v: True)
        self.assertFalse(confirmed)
        self.assertIn("names none of the lemma's variables (x)", reason)


SIMILAR_TASK = ("# Goal\n\nprove it\n\n## Similar closed lemmas\n\n### one\n\nA\n\n### two\n\nB\n\n### three\n\nC\n\n"
                "## Answer form\n\nJSON\n")


class BestOfNTests(DriveBase):
    """haiku-low with three samples per round: varied prompts, the first sample the kernel accepts closes the
    goal, a round is one ladder step, and the accounting."""

    def setUp(self):
        super().setUp()
        drive.tier_rows = legacy_rows(self.saved_rows, **{"haiku-low": dict(samples=3)})

    def test_sample_prompts_differ_and_are_deterministic(self):
        prompts = [drive.sample_prompt(SIMILAR_TASK, "fn/meaning/lemA", i, 3) for i in range(3)]
        self.assertEqual(len(set(prompts)), 3)
        self.assertEqual(prompts, [drive.sample_prompt(SIMILAR_TASK, "fn/meaning/lemA", i, 3) for i in range(3)])
        self.assertEqual(drive.sample_prompt(SIMILAR_TASK, "fn/meaning/lemA", 0, 1), SIMILAR_TASK)
        order = [[name for name in ("### one", "### two", "### three") if name in p] for p in prompts]
        self.assertEqual([sorted(p.index(n) for n in o) == [p.index(n) for n in o] for p, o in zip(prompts, order)],
                         [True, False, False])
        self.assertLess(prompts[1].index("### two"), prompts[1].index("### one"))
        self.assertLess(prompts[2].index("### three"), prompts[2].index("### one"))
        families = {next(f for f in drive.FAMILIES if f in p) for p in prompts}
        self.assertEqual(len(families), 3)
        for p, i in zip(prompts, range(3)):
            self.assertIn("## Sample %d of 3" % (i + 1), p)
            self.assertLess(p.index("## Sample"), p.index("## Answer form"))
            self.assertEqual(p.count("A\n") + p.count("B\n") + p.count("C\n"), 3)

    def test_samples_from_routing_json(self):
        saved = drive.route.load_routing
        drive.route.load_routing = lambda: {"*": {"samples": {"haiku-low": 2}}}
        try:
            self.assertEqual((drive.samples("haiku-low"), drive.samples("haiku-high")), (2, 1))
        finally:
            drive.route.load_routing = saved
        self.assertEqual(drive.samples("haiku-low"), 3)

    def test_first_accepted_sample_closes_the_goal(self):
        self.install(lambda prompt: BAD if "## Sample 1 of 3" in prompt else GOOD)
        summary = drive_kernel.run_round(F, self.run_dir, tier="haiku-low", kernel=self.kernel)
        self.assertEqual((summary["started"], summary["goals"]), (3, 1))
        prompts = [h.prompt for _, _, h in self.agents.spawned]
        self.assertEqual(len({drive.sha(p) for p in prompts}), 3)
        item = self.state()[self.sid("lemA")]
        self.assertEqual((item["state"], item["closed_by"], item["events"][-1]["attempt"]), ("closed", "haiku-low", 2))
        results = {e["attempt"]: e["class"] for e in item["events"] if e.get("tier") == "haiku-low"
                   and e["state"] == "failed"}
        self.assertEqual(results, {1: "compile_error", 3: drive.SUPERSEDED})
        self.assertEqual(summary["verdicts"], {"proved": 3})
        where = drive.locate(self.run_dir, F)[self.sid("lemA")]
        self.assertEqual(json.loads(where.answer_json.read_text())["attempt"], 2)
        self.assertEqual(sorted(p.name for p in (where.d / "samples" / "lemA").iterdir()),
                         ["haiku-low-1.json", "haiku-low-2.json", "haiku-low-3.json"])
        # Sample 1 failed its final check, sample 2 passed it; sample 3 was never compiled.
        finals = [(out.parent.name, proof) for _, out, proof in self.compiled if out.name == "final"]
        self.assertEqual([name for name, _ in finals], ["haiku-low-1", "haiku-low-2"])
        self.assertEqual(drive.route.attempt_results(item)["haiku-low"], ["closed"])
        running = [e for e in item["events"] if e["state"] == "running" and e["tier"] == "haiku-low"]
        self.assertEqual([e["context_items"][-2:] for e in running[:3]],
                         [["sample:%d/3" % i, "round:1"] for i in (1, 2, 3)])

    def test_a_failed_round_is_one_ladder_step(self):
        self.install(BAD)
        drive_kernel.run_round(F, self.run_dir, tier="haiku-low", kernel=self.kernel)
        item = self.state()[self.sid("lemA")]
        self.assertEqual(drive.route.attempt_results(item)["haiku-low"], ["compile_error"])
        self.assertEqual(drive.model_items(self.run_dir, F)[0],
                         (self.sid("lemA"), "haiku-low", "again with the compiler error text"))
        first = [h.prompt for _, _, h in self.agents.spawned]
        self.install(BAD)
        summary = drive_kernel.run_round(F, self.run_dir, tier="haiku-low", kernel=self.kernel)
        self.assertEqual(summary["started"], 3)
        second = [h.prompt for _, _, h in self.agents.spawned]
        self.assertTrue(all("wrong_tactic was not found" in p for p in second))
        self.assertEqual(len({drive.sha(p) for p in first + second}), 6)
        item = self.state()[self.sid("lemA")]
        self.assertEqual(item["tier_attempts"]["haiku-low"], 6)
        self.assertEqual(drive.route.attempt_results(item)["haiku-low"], ["compile_error", "compile_error"])
        self.assertEqual([t for _, t, _ in drive.model_items(self.run_dir, F)], ["haiku-high"])
        self.assertEqual(dict(report.measures(self.run_dir, F))["spin"], "0")

    def test_accounting_per_tier(self):
        self.install(lambda prompt: BAD if "## Sample 1 of 3" in prompt else GOOD)
        drive_kernel.run_round(F, self.run_dir, tier="haiku-low", kernel=self.kernel)
        lines = dict(report.measures(self.run_dir, F))
        self.assertEqual(lines["cost haiku-low"],
                         "goals closed 1, attempts 3, best-of-N rounds 1 with 3 samples, tool calls check 0 lookup 0 "
                         "search 0 counterexample 0, tokens 3840, tokens per closed goal 3840.0, cost weight 1 "
                         "(placeholder), cost-weighted tokens per closed goal 3840.0")
        self.assertNotIn("cost haiku-high", lines)
        self.assertEqual(report.cost_line([self.state()[self.sid("lemA")]], "opus-medium", 30), None)


if __name__ == "__main__":
    unittest.main()
