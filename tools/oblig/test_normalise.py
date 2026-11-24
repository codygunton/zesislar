"""Goal normaliser: probe records, link and composed proofs, the snapshot screen, parts as goals, and
real Rocq runs (unfold + generalise, link lemma, fallback levels, split ids, snapshot verdicts) on a
fixture module in the ZesuSsz namespace when a bank with ResidualExport is at hand."""
import json
import os
import shutil
import subprocess
import sys
import tempfile
import unittest
from pathlib import Path

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[1]
sys.path.insert(0, str(HERE))
sys.path.insert(0, str(ROOT / "tools/block"))
sys.path.insert(0, str(ROOT / "tools/residuals"))
import falsify  # noqa: E402
import normalise  # noqa: E402
import store  # noqa: E402
import render_residual_module as rrm  # noqa: E402
import check_relocatable  # noqa: E402
import residual_loop as rl  # noqa: E402
import symbolize  # noqa: E402
from test_symbolize import BOUNDS, TEXT_END, TEXT_START, disjoint  # noqa: E402

LOG = """0.1 noise
0.2 @@N part 1 binders x H0
0.3 @@N part 1 stmt (forall (x : Z), (H0 : x = 0) -> x <= 0)
0.4 @@N part 2 binders y
0.5 @@N part 2 stmt (forall (y : Z), 0 <= y * y)
0.6 @@N link intros. destruct H as [Hn Hn0]. split; [ exact (zn_part_1 (f a) Hn) | exact (zn_part_2 (g a)) ]
0.7 @@N done 2 2
0.8 @@N part 1 refused unsupported syntax
0.9 @@N link intros. fail.
1.0 @@N done 1 1
"""


class ProbeTests(unittest.TestCase):
    def test_levels_parts_and_refusals_parse(self):
        found = normalise.parse_probe(LOG)
        self.assertTrue(found[2]["complete"])
        self.assertEqual([p["k"] for p in found[2]["parts"]], [1, 2])
        self.assertEqual(found[2]["parts"][0]["binders"], ["x", "H0"])
        self.assertTrue(found[2]["link"].startswith("intros. destruct H"))
        self.assertFalse(found[1]["complete"])
        self.assertEqual(found[1]["refused"], ["part 1: unsupported syntax"])

    def test_link_lemma_states_parts_then_goal(self):
        parts = normalise.parse_probe(LOG)[2]["parts"]
        text = normalise.link_text(["Require Import A."], "G", parts, "LINK.")
        self.assertIn("Lemma zn_link :\n  ((forall (x : Z), (H0 : x = 0) -> x <= 0)) ->\n  "
                      "((forall (y : Z), 0 <= y * y)) ->\n  (G).", text)
        self.assertIn("intros zn_part_1 zn_part_2.\nLINK.\nQed.", text)

    def test_composed_proof_copies_part_proofs_byte_for_byte(self):
        parts = [dict(k=1, statement="P1"), dict(k=2, statement="P2")]
        proofs = ["intros.\n  - lia.\nQed.\n", "  auto.\nQed."]
        text = normalise.composed_proof(parts, "LINK.", proofs)
        self.assertEqual(text, "assert (zn_part_1 :\n  P1).\n{ intros.\n  - lia.\n}\n"
                               "assert (zn_part_2 :\n  P2).\n{   auto.\n}\nLINK.\nQed.\n")
        with self.assertRaises(normalise.NormaliseError):
            normalise.composed_proof(parts[:1], "LINK.", ["auto."])

    def test_worst_verdicts(self):
        self.assertEqual(normalise.worst_screen(["true-on-3-states", "false-on-real-state(a)"]), "false-on-real-state(a)")
        self.assertEqual(normalise.worst_screen(["true-on-3-states", "true-on-1-states"]), "true-on-1-states")
        self.assertEqual(normalise.worst_falsify(["passed", "unchecked"]), "unchecked")


def snapshot(directory, offset, regs, memory, visits=1):
    directory.mkdir(parents=True, exist_ok=True)
    rows = [dict(visit=k, insn=k, regs=dict(regs, a0=regs.get("a0", 0) + k), memory=[
        dict(name=name, base=base, size=len(data), hex=data.hex()) for name, (base, data) in memory.items()])
        for k in range(visits)]
    (directory / ("STATE-%s.json" % offset)).write_text(json.dumps(dict(schema="oblig-exec-snapshot/1", visits=rows)))


MAP = dict(schema="oblig-exec-binders/1", function="demo", mode="remap-never", binders=[
    dict(pattern=r"(^|_)resultPointer$", source=dict(reg="a0", at="entry")),
    dict(pattern=r"(^|_)list_len$", source=dict(mem="list", offset=8, size=8, at="entry")),
    dict(pattern=r"(^|_)list_items$", source=dict(deref=dict(mem="list", offset=0, size=8),
                                                  length=dict(mem="list", offset=8, size=8), scale=2, at="entry")),
    dict(pattern=r"^machine_x(\d+)$", source=dict(reg=r"x\1", at="block")),
    dict(pattern=r"^b$", source=dict(const=0))])


class ScreenRowTests(unittest.TestCase):
    def setUp(self):
        self.tmp = Path(tempfile.mkdtemp())
        header = (0x1000).to_bytes(8, "little") + (2).to_bytes(8, "little") + (4).to_bytes(8, "little")
        memory = dict(list=(0x800, header), heap=(0x1000, bytes(range(16))))
        for name in ("len2.remap-never", "len2.alloc-fail-1.remap-never", "len2"):
            snapshot(self.tmp / name, "0000", dict(a0=7, a1=0x800), memory)
            snapshot(self.tmp / name, "0010", dict(a0=99, a5=55), memory, visits=2)

    def tearDown(self):
        shutil.rmtree(self.tmp)

    def test_states_of_the_run_mode_only_one_per_visit(self):
        states = normalise.snapshot_states(self.tmp, "0010", "remap-never")
        self.assertEqual([(s[0], s[1]) for s in states], [("len2.remap-never", 0), ("len2.remap-never", 1)])

    def test_values_by_projection_path(self):
        states = normalise.snapshot_states(self.tmp, "0010", "remap-never")
        binders = [dict(name="base_resultPointer", kind="bv", width=64), dict(name="H", kind="prop"),
                   dict(name="base_list_len", kind="Z"), dict(name="base_list_items", kind="bytes"),
                   dict(name="machine_x15", kind="bv", width=64), dict(name="b", kind="Z")]
        rows, missing = normalise.screen_rows(binders, states, MAP)
        self.assertEqual(missing, [])
        self.assertEqual(rows[0]["values"], dict(base_resultPointer=7, base_list_len=2,
                                                 base_list_items=dict(hex=bytes(range(4)).hex()),
                                                 machine_x15=55, b=0))
        self.assertEqual(rows[1]["origin"], "len2.remap-never#1")

    def test_unmapped_binders_are_named(self):
        states = normalise.snapshot_states(self.tmp, "0010", "remap-never")
        rows, unmapped = normalise.screen_rows([dict(name="mystery", kind="Z")], states, MAP)
        self.assertEqual((rows, unmapped), ([], ["mystery"]))

    def test_snapshot_bytes_print_as_a_closed_list(self):
        text = falsify.coq_value(dict(name="l", kind="bytes"), dict(hex="0102"))
        self.assertIn("(@Coq.Init.Datatypes.cons Coq.Numbers.BinNums.Z (1)%Z (@Coq.Init.Datatypes.cons", text)

    def test_seeded_maps_load(self):
        for function in ("keysToOwnedSlice", "entriesToOwnedSlice", "keysEnsureCapacity"):
            data = normalise.load_binder_map(function)
            self.assertEqual(data["mode"], "remap-never")
            self.assertIsNotNone(normalise.map_binder("keysBase_toOwnedList_arrayListLength", data["binders"])[0]
                                 if function != "keysEnsureCapacity" else
                                 normalise.map_binder("ensureBase_ensureList_arrayListLength", data["binders"])[0])


def residual_run(root, block="0010"):
    """A residual_loop run dir with goal 0010-1 normalised into parts 0010-2 and 0010-3."""
    run = root / "resid" / block
    bank = root / "bank"
    (bank / "install/default/lib").mkdir(parents=True)
    (bank / "ARGS.json").write_text(json.dumps(["coqc"]))
    header = "Require Import ZesuSsz.Demo.\nLocal Open Scope Z_scope."
    goals = []
    for gid, statement in (("%s-1" % block, "G"), ("%s-2" % block, "P1"), ("%s-3" % block, "P2")):
        d = run / "goals" / gid
        d.mkdir(parents=True)
        name = "residual_demo_%s_%s" % (block, normalise.sha(statement)[:16])
        (d / "goal.v").write_text("%s\n\nLemma %s :\n  %s.\nProof.\n%s\nAdmitted.\n"
                                  % (header, name, statement, rrm.SLOT))
        goals.append(dict(id=gid, name=name, statement=statement, reparse="exact"))
    goals[0].update(parts=["%s-2" % block, "%s-3" % block], normalised=dict(level=2, link="LINK."))
    goals[1].update(part_of="%s-1" % block, part=1)
    goals[2].update(part_of="%s-1" % block, part=2)
    (run / "MANIFEST.json").write_text(json.dumps(dict(block=block, function="demo", bank=str(bank), goals=goals)))
    return run


def close(run, gid, proof, full=None):
    d = run / "goals" / gid
    head = (d / "goal.v").read_text().split("(* PROOF-SLOT")[0]
    (d / "proof.v").write_text(head + proof)
    if full:
        (d / "full-proof.v").write_text(head + full)
    (d / "STATUS.json").write_text(json.dumps(dict(attempts=[], result="PASS")))


class PartsTests(unittest.TestCase):
    def setUp(self):
        self.tmp = Path(tempfile.mkdtemp())
        self.run = residual_run(self.tmp)

    def tearDown(self):
        shutil.rmtree(self.tmp)

    def test_compose_waits_for_every_part_and_uses_the_full_proof(self):
        close(self.run, "0010-2", "minimised.\nQed.\n", full="intros; lia.\nQed.\n")
        self.assertEqual(normalise.compose(self.run), [])
        close(self.run, "0010-3", "auto.\nQed.\n")
        self.assertEqual(normalise.compose(self.run), ["0010-1"])
        text = (self.run / "answers" / "0010-1.v").read_text()
        self.assertEqual(text, "assert (zn_part_1 :\n  P1).\n{ intros; lia.\n}\n"
                               "assert (zn_part_2 :\n  P2).\n{ auto.\n}\nLINK.\nQed.\n")
        # Literal-free parts: the goal.v header stays as it was.
        self.assertNotIn(symbolize.REQUIRE, (self.run / "goals" / "0010-1" / "goal.v").read_text())
        self.assertFalse((self.run / "goals" / "0010-1" / "goal-norequire.v").exists())

    def test_compose_names_section_bounds_and_imports_their_notations(self):
        statement = "(forall (x n : Z), %s)" % disjoint("x", TEXT_START, TEXT_END)
        manifest = json.loads((self.run / "MANIFEST.json").read_text())
        manifest["goals"][1]["statement"] = statement
        manifest["goals"][0]["normalised"]["link"] = "exact (zn_part_1 (%d)%%Z)." % (TEXT_START + 0x10)
        (self.run / "MANIFEST.json").write_text(json.dumps(manifest))
        close(self.run, "0010-2", "intros; lia.\nQed.\n")
        close(self.run, "0010-3", "auto.\nQed.\n")
        saved = symbolize.table, symbolize.sections
        symbolize.table = lambda path=None: [(TEXT_START + 0x10, "sym_demo")]
        symbolize.sections = lambda path=None: BOUNDS
        try:
            self.assertEqual(normalise.compose(self.run), ["0010-1"])
        finally:
            symbolize.table, symbolize.sections = saved
        text = (self.run / "answers" / "0010-1.v").read_text()
        self.assertIn("(sec_text_start)%Z", text)
        self.assertIn("(sec_text_end)%Z", text)
        self.assertIn("exact (zn_part_1 (sym_demo)%Z).", text)
        self.assertEqual(check_relocatable.address_hits(text), [])
        d = self.run / "goals" / "0010-1"
        goal_v = (d / "goal.v").read_text()
        self.assertEqual(goal_v.split("\n")[:3],
                         ["Require Import ZesuSsz.Demo.", symbolize.REQUIRE, "Local Open Scope Z_scope."])
        original = (d / "goal-norequire.v").read_text()
        self.assertEqual(goal_v[goal_v.index("\nLemma "):], original[original.index("\nLemma "):])
        # collect fills proof.v from goal.v and register takes the module header from it.
        (d / "proof.v").write_text(rl.goal_head(goal_v) + text)
        self.assertIn(symbolize.REQUIRE, rrm.read_goal(d)[0])

    def test_collect_refuses_an_answer_naming_an_address(self):
        self.assertIn("absolute address", rl.answer_problems("assert (x = %#x) by lia.\nQed.\n" % TEXT_END))
        self.assertIsNone(rl.answer_problems("assert (x = sec_text_end) by lia.\nQed.\n"))

    def test_store_blocks_the_goal_on_its_first_open_part(self):
        states = store.derived_states("demo", self.tmp)
        parent = store.goal_id("demo", "0010", "G")
        self.assertEqual(states[parent][2:4], ("blocked-on", store.goal_id("demo", "0010", "P1")))
        close(self.run, "0010-2", "auto.\nQed.\n")
        states = store.derived_states("demo", self.tmp)
        self.assertEqual(states[parent][2:4], ("blocked-on", store.goal_id("demo", "0010", "P2")))
        store.sync("demo", self.tmp)
        state = store.fold(store.read_events(self.tmp))
        self.assertEqual((state[parent]["state"], state[parent]["blocked_by"]),
                         ("blocked-on", store.goal_id("demo", "0010", "P2")))

    def test_parts_are_never_rendered(self):
        manifest = self.run / "MANIFEST.json"
        self.assertEqual(rrm.goal_ids(None, "0010", manifest), ["0010-1"])

    def test_apply_adds_parts_with_ids_of_their_own(self):
        run = residual_run(self.tmp / "other", block="0020")
        manifest = json.loads((run / "MANIFEST.json").read_text())
        manifest["goals"] = manifest["goals"][:1]
        del manifest["goals"][0]["parts"], manifest["goals"][0]["normalised"]
        out = self.tmp / "norm"
        record = dict(level=2, link="LINK.", link_file="link.v", parts=[])
        for k, statement in ((1, "(forall (x : Z), x = x)"), (2, "(forall (y : Z), y = y)")):
            goal = out / ("part-%d" % k) / "goal.v"
            (goal.parent / "screen").mkdir(parents=True)
            (goal.parent / "screen" / "SCREEN.json").write_text("{}")
            record["parts"].append(dict(k=k, name="residual_demo_0020_%s" % normalise.sha(statement)[:16],
                                        statement=statement, binders=["x"], goal=str(goal)))
        ids = normalise.apply(run, manifest, manifest["goals"][0], record,
                              reparse=lambda *args: dict(reparse="exact"))
        self.assertEqual(ids, ["0020-2", "0020-3"])
        saved = json.loads((run / "MANIFEST.json").read_text())
        self.assertEqual(saved["goals"][0]["parts"], ids)
        self.assertEqual([g.get("part_of") for g in saved["goals"]], [None, "0020-1", "0020-1"])
        self.assertNotEqual(store.goal_id("demo", "0020", saved["goals"][1]["statement"]),
                            store.goal_id("demo", "0020", saved["goals"][2]["statement"]))
        self.assertTrue((run / "goals" / "0020-2" / "screen" / "SCREEN.json").is_file())
        self.assertIn("forall (y : Z)", (run / "goals" / "0020-3" / "goal.v").read_text())

    def test_drive_closes_the_goal_by_its_composed_proof(self):
        import drive
        close(self.run, "0010-2", "auto.\nQed.\n")
        close(self.run, "0010-3", "auto.\nQed.\n")
        store.sync("demo", self.tmp)
        parent = store.goal_id("demo", "0010", "G")
        located = drive.locate(self.tmp, "demo")
        state = store.fold(store.read_events(self.tmp))
        self.assertEqual(sorted(drive.dependencies("demo", state[parent], located[parent])),
                         sorted([store.goal_id("demo", "0010", "P1"), store.goal_id("demo", "0010", "P2")]))

        class Kernel:
            checked = []

            def check(self, d, gids, jobs):
                self.checked.append(((Path(d) / "answers" / (gids[0] + ".v")).read_text()))
                return {gids[0]: "PASS"}
        kernel = Kernel()
        counts = drive.Counts()
        self.assertEqual(drive.compose_parents("demo", self.tmp, state, located, kernel, counts), 1)
        self.assertIn("assert (zn_part_2 :\n  P2).", kernel.checked[0])
        state = store.fold(store.read_events(self.tmp))
        self.assertEqual((state[parent]["state"], state[parent]["closed_by"]), ("closed", "normalise"))


# ---- Rocq ----

def find_bank():
    """A bank whose ZesuSsz holds Automation2/ResidualExport.vo (ZESU_NORMALISE_BANK, else _build/banks)."""
    if os.environ.get("ZESU_NORMALISE_BANK"):
        bank = Path(os.environ["ZESU_NORMALISE_BANK"])
        return bank if (bank / "ARGS.json").is_file() else None
    proc = subprocess.run(["git", "rev-parse", "--git-common-dir"], cwd=ROOT, capture_output=True, text=True)
    main = (ROOT / proc.stdout.strip()).resolve().parent if proc.returncode == 0 else ROOT
    for args in sorted((main / "_build/banks").glob("*/ARGS.json"), reverse=True):
        data = json.loads(args.read_text())
        zesu = [data[i + 1] for i, a in enumerate(data) if a == "-Q" and i + 2 < len(data) and data[i + 2] == "ZesuSsz"]
        if zesu and (Path(zesu[0]) / "Automation2/ResidualExport.vo").is_file() and Path(data[0]).exists():
            return args.parent
    return None


FIXTURE = r"""From Coq Require Import ZArith.ZArith.
From stdpp Require Import base.
Local Open Scope Z_scope.
Record Inner : Type := { innerLen : Z; innerCap : Z }.
Record Args : Type := { argsInner : Inner; argsPtr : Z }.
Definition argsLen (a : Args) : Z := innerLen (argsInner a).
Definition dom (a : Args) : Prop :=
  0 <= argsLen a <= innerCap (argsInner a) /\ exists w : Z, w = argsPtr a /\ 0 <= w.
Definition hidden_def (P : Prop) : Prop := P.
Definition hidden_aux : seal (@hidden_def). Proof. eexists. reflexivity. Qed.
Definition hidden : Prop -> Prop := hidden_aux.(unseal).
Lemma hidden_eq : hidden = hidden_def. Proof. exact (seal_eq hidden_aux). Qed.
Global Opaque hidden.
Definition post (a : Args) : Prop := argsLen a <= innerCap (argsInner a) /\ 0 <= argsPtr a + innerLen (argsInner a).
"""
HEADER = ["From Coq Require Import ZArith.ZArith.", "Require Import stdpp.bitvector.tactics.", "Require Import ZesuSsz.Automation2.All.",
          "Require Import ZesuSsz.NormFixture.Defs.",
          "Local Open Scope Z_scope."]
D = "@ZesuSsz.NormFixture.Defs."
TRUE_GOAL = ("(forall (a : (%sArgs)), (forall (H0 : (%sdom a)), (forall (H1 : (%shidden (@Coq.ZArith.BinInt.Z.le (0)%%Z "
             "(%sargsPtr a)))), (%spost a))))" % (D, D, D, D, D))
FALSE_GOAL = ("(forall (a : (%sArgs)), (forall (H0 : (%sdom a)), (@Coq.ZArith.BinInt.Z.le (%sargsPtr a) (5)%%Z)))"
              % (D, D, D))


@unittest.skipUnless(find_bank(), "no bank with ZesuSsz.Automation2.ResidualExport (set ZESU_NORMALISE_BANK)")
class RocqTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.tmp = Path(tempfile.mkdtemp())
        fixture = cls.tmp / "fixture"
        fixture.mkdir()
        (fixture / "Defs.v").write_text(FIXTURE)
        bank = cls.tmp / "bank"
        bank.mkdir()
        args = json.loads((find_bank() / "ARGS.json").read_text())
        args += ["-Q", str(fixture), "ZesuSsz.NormFixture"]
        (bank / "ARGS.json").write_text(json.dumps(args))
        route = falsify.Route(bank, direct=True)
        proc = subprocess.run(route.args + ["Defs.v"], cwd=fixture, capture_output=True, text=True)
        assert proc.returncode == 0, proc.stdout + proc.stderr
        cls.route = route

    @classmethod
    def tearDownClass(cls):
        shutil.rmtree(cls.tmp)

    def goal(self, gid, statement, status="OPEN"):
        run = self.tmp / ("run-" + gid)
        d = run / "goals" / gid
        d.mkdir(parents=True)
        name = "residual_demo_0010_" + normalise.sha(statement)[:16]
        (d / "goal.v").write_text("%s\n\nLemma %s :\n  %s.\nProof.\n%s\nAdmitted.\n"
                                  % ("\n".join(HEADER), name, statement, rrm.SLOT))
        (d / "STATUS.json").write_text(json.dumps(dict(attempts=[], result=status)))
        goal = dict(id=gid, name=name, statement=statement, reparse="exact")
        return run, dict(block="0010", function="demo", bank=str(self.tmp / "bank"), goals=[goal]), goal

    def test_unfold_generalise_split_and_link(self):
        run, manifest, goal = self.goal("0010-1", TRUE_GOAL)
        exec_dir = self.tmp / "exec"
        snapshot(exec_dir / "in1.remap-never", "0000", dict(a0=3), {})
        snapshot(exec_dir / "in1.remap-never", "0010", dict(a0=3), {})
        snapshot(exec_dir / "in2.remap-never", "0000", dict(a0=4), {})
        snapshot(exec_dir / "in2.remap-never", "0010", dict(a0=4), {})
        binder_map = dict(schema="oblig-exec-binders/1", mode="remap-never", binders=[
            dict(pattern=r"^argsPtr$", source=dict(reg="a0", at="entry")),
            dict(pattern=r"^argsInner_innerLen$", source=dict(const=1)),
            dict(pattern=r"^argsInner_innerCap$", source=dict(const=2)),
            dict(pattern=r"^w$", source=dict(reg="a0", at="entry"))])
        states = normalise.snapshot_states(exec_dir, "0010", "remap-never")
        record = normalise.normalise_goal(run, manifest, goal, self.route, run / "normalise", states, binder_map,
                                          run_mechanical=True)
        self.assertEqual(record["level"], 2)
        self.assertEqual(record["levels"]["2"]["link"], "PASS")
        self.assertEqual(len(record["parts"]), 2)
        for part in record["parts"]:
            self.assertNotIn("Args", part["statement"])
            self.assertNotIn("dom", part["statement"])
            self.assertNotIn("hidden", part["statement"])
            self.assertEqual(part["screen"], "true-on-2-states")
        self.assertIn("argsInner_innerLen", record["parts"][0]["binders"])
        self.assertNotEqual(record["parts"][0]["sha256"], record["parts"][1]["sha256"])
        self.assertIn("rewrite @ZesuSsz.NormFixture.Defs.hidden_eq in H1.", record["link"])
        self.assertTrue(record["mechanical_after"])
        # The link is required: a wrong part statement does not compile.
        found = normalise.parse_probe((run / "normalise" / "0010-1" / "probe.log").read_text())
        parts = [dict(p, statement=p["statement"].replace("(0)%Z", "(1)%Z")) for p in found[2]["parts"]]
        bad = run / "bad-link.v"
        bad.write_text(normalise.link_text(HEADER, TRUE_GOAL, parts, found[2]["link"]))
        self.assertFalse(normalise.compile_ok(self.route, bad, "bad-link")[0])
        # The composed proof of the parts proves the goal itself.
        proofs = ["intros; lia.\nQed.\n"] * 2
        composed = run / "composed.v"
        composed.write_text("%s\n\nLemma composed :\n  %s.\nProof.\n%s"
                            % ("\n".join(HEADER), TRUE_GOAL, normalise.composed_proof(record["parts"], record["link"], proofs)))
        self.assertTrue(normalise.compile_ok(self.route, composed, "composed")[0])

    def test_a_refuted_level_falls_back_and_the_screen_names_the_input(self):
        run, manifest, goal = self.goal("0010-2", FALSE_GOAL)
        exec_dir = self.tmp / "exec-false"
        snapshot(exec_dir / "small.remap-never", "0000", dict(a0=3), {})
        snapshot(exec_dir / "small.remap-never", "0010", dict(a0=3), {})
        snapshot(exec_dir / "big.remap-never", "0000", dict(a0=9), {})
        snapshot(exec_dir / "big.remap-never", "0010", dict(a0=9), {})
        binder_map = dict(schema="oblig-exec-binders/1", mode="remap-never", binders=[
            dict(pattern=r"^argsPtr$", source=dict(reg="a0", at="entry")),
            dict(pattern=r"^w$", source=dict(reg="a0", at="entry")),
            dict(pattern=r"^argsInner_inner(Len|Cap)$", source=dict(const=0))])
        states = normalise.snapshot_states(exec_dir, "0010", "remap-never")
        record = normalise.normalise_goal(run, manifest, goal, self.route, run / "normalise", states, binder_map)
        # The real state refutes the level-2 part: kept, with the input named.
        self.assertEqual(record["level"], 2)
        self.assertEqual(record["screen"], "false-on-real-state(big.remap-never)")
        # Without snapshots falsify.py's refutation sends the goal to level 1 (the record binder kept).
        record = normalise.normalise_goal(run, manifest, goal, self.route, run / "normalise-nosnap", [], binder_map)
        self.assertEqual(record["levels"]["2"]["falsify"], ["false"])
        self.assertEqual(record["levels"]["2"]["fallback"], "falsify.py refuted a part")
        self.assertEqual(record["level"], 1)
        self.assertEqual(record["screen"], "not-evaluable")


if __name__ == "__main__":
    unittest.main()
