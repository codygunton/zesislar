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
    def __init__(self, reply):
        self.reply, self.spawned, self.writes = reply, [], []
        agents = self

        class Tool:
            async def write(self, args):
                agents.writes.append(args)
        self.tool = Tool()

    def agent(self, prompt, agent=None, label=None):
        handle = FakeHandle(prompt, self.reply(prompt) if callable(self.reply) else self.reply)
        self.spawned.append((agent, label, handle))
        return handle

    def wait(self, handles, raise_errors=True):
        return [h.reply for h in handles]


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
        self.install(GOOD)

    def tearDown(self):
        dispatch_kernel.usage = self.saved
        for name in ("agent", "wait", "tool"):
            drive_kernel.__dict__.pop(name, None)
        self.tmp.cleanup()

    def install(self, reply):
        self.agents = FakeAgents(reply)
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
        self.assertTrue(prompt.startswith(drive.NO_TOOLS))
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
        self.install(GIVE_UP)
        drive_kernel.run_round(F, self.run_dir, tier="haiku-low", kernel=self.kernel)
        self.assertEqual([t for _, t, _ in drive.model_items(self.run_dir, F)], ["haiku-medium"])
        with self.assertRaises(drive_kernel.DriveError):
            drive_kernel.run_round(F, self.run_dir, tier="haiku-medium", kernel=self.kernel)
        summary = drive_kernel.run_round(F, self.run_dir, kernel=self.kernel)
        self.assertEqual((summary["started"], list(summary["skipped"])), (0, ["haiku-medium"]))
        asyncio.run(drive_kernel.set_tier_override("haiku-medium"))
        self.assertEqual(json.loads(self.agents.writes[-1]["content"])["scout"], "anthropic/claude-haiku-5-5:medium")
        self.install(GOOD)
        summary = drive_kernel.run_round(F, self.run_dir, tier="haiku-medium", kernel=self.kernel)
        self.assertEqual(summary["started"], 1)
        self.assertEqual(self.agents.spawned[0][0], "scout")
        self.assertEqual(self.state()[self.sid("lemA")]["closed_by"], "haiku-medium")


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


if __name__ == "__main__":
    unittest.main()
