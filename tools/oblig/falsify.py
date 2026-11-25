#!/usr/bin/env python3
"""Falsity check of a pure goal: a fixed list of concrete assignments, each decided in Rocq.

    falsify.py check GOAL.v --bank BANK [--ocamlpath DIR] [--lemma NAME] [--out DIR]
                     [--exec-dir RUN/exec --offset OFF] [--limit 200]

GOAL.v is a residual goal (`Lemma <name> :` statement `.` then `Proof.`), a leftover
goal file (`Goal <statement>.`, fully qualified names, no imports), or a rendered
residual module with --lemma naming one of its lemmas. The statement is
`forall <binders>, <conclusion>`; premises are the binders whose type is a Prop.

Three compiles, each in its own resource-guard scope (the route of
tools/block/residual_loop.py):
1. probe: Rocq walks the binders of the statement and prints the kind of each one
   (Z, nat, N, bool, bv <w>, list of bv 8, a Prop, a record, other; a type alias by its head
   normal form). A record binder whose type tools/oblig/records.json registers is projected
   to its fields (each a checked kind or a registered record; a field variable is named by its
   projection path, as tools/oblig/normalise.py names them) and the search builds the record
   from them; any other record binder makes the verdict `unchecked` with reason
   `unscreened: record binder <name> : <type>`, a data binder of any other type `unchecked`
   too; nothing else runs.
2. search: at most LIMIT (200) assignments, fixed by the statement alone. Values: 0, 1,
   each literal of the statement and its neighbours, 2^k - 1 and 2^k for k in 8, 16,
   32, 64, the RAM bounds 0xa0000000 and 0xc0000000, byte lists of length 0, 1, 55
   and 56, and, for binders named after a machine register or a contract argument,
   the values of the machine-run snapshots RUN/exec/<input id>/STATE-<offset>.json.
   For each assignment Rocq instantiates the data binders in order, decides each
   premise with `bool_decide` and `vm_compute`, and then decides the negated
   conclusion the same way. No machine code runs and no symbolic search happens.
3. kernel check of the first hit: `Lemma zf_refute : ~ <statement>.` proved by the
   same steps and closed by `Qed.`, then `Print Assumptions zf_refute`.

Verdicts (FALSIFY.json in --out, default beside GOAL.v):
- `false`: an assignment satisfies every premise and refutes the conclusion; the
  kernel accepted `zf_refute` (refute.v holds the counterexample).
- `passed`: no assignment refutes the statement (this is not a proof).
- `unchecked`: a data binder has a type outside the list, or no assignment could be
  decided (a premise or the conclusion has no `Decision` instance or does not reduce).
"""
import argparse
import hashlib
import json
import random
import resource
import re
import subprocess
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(ROOT / "tools/block"))
import residual_loop as rl  # noqa: E402
RECORDS_FILE = Path(__file__).resolve().parent / "records.json"

LIMIT = 200
CLAIM = 2 << 30
DIRECT_GIB = 4
RAM_BOUNDS = (0xa0000000, 0xc0000000)
POWERS = (8, 16, 32, 64)
BYTE_LENGTHS = (0, 1, 55, 56)
NAT_MAX = 4096  # nat literals are unary terms; larger values are not instantiated
REGISTER = re.compile(r"(?:^|_)(x(?:[12]?\d|3[01])|zero|ra|sp|gp|tp|t[0-6]|s(?:\d|1[01])|a[0-7]|fp)$")
ABI = dict([("zero", "x0"), ("ra", "x1"), ("sp", "x2"), ("gp", "x3"), ("tp", "x4"), ("t0", "x5"), ("t1", "x6"),
            ("t2", "x7"), ("s0", "x8"), ("fp", "x8"), ("s1", "x9")]
           + [("a%d" % i, "x%d" % (10 + i)) for i in range(8)]
           + [("s%d" % i, "x%d" % (16 + i)) for i in range(2, 12)]
           + [("t%d" % i, "x%d" % (25 + i)) for i in range(3, 7)])
CHECKED_KINDS = ("Z", "nat", "N", "bool", "bv", "bytes", "prop")

# Loaded before the goal's own preamble, so that the goal's imports keep their precedence;
# the Imports activate the %Z and %N keys of the generated values and stdpp's Decision instances.
REQUIRES = ("From Coq Require Import ZArith.ZArith NArith.NArith.\nFrom Coq Require Lists.List ZArith.Znumtheory.\n"
            "From stdpp Require Import base decidable numbers list bitvector.definitions.\n")

LTAC = r"""
(* stdpp has no Decision instance for Z.divide (`(8 | p)` facts of the contracts). *)
#[local] Instance zf_Z_divide_dec (a b : Coq.Numbers.BinNums.Z) :
  stdpp.base.Decision (Coq.ZArith.BinInt.Z.divide a b) := Coq.ZArith.Znumtheory.Zdivide_dec a b.
Ltac zf_kind H T :=
  lazymatch type of T with
  | Prop => idtac "@@ZF B" H "prop"
  | _ => lazymatch T with
    | Coq.Numbers.BinNums.Z => idtac "@@ZF B" H "Z"
    | Coq.Init.Datatypes.nat => idtac "@@ZF B" H "nat"
    | Coq.Numbers.BinNums.N => idtac "@@ZF B" H "N"
    | Coq.Init.Datatypes.bool => idtac "@@ZF B" H "bool"
    | stdpp.bitvector.definitions.bv ?n =>
        let w := eval vm_compute in (Coq.ZArith.BinInt.Z.of_N n) in idtac "@@ZF B" H "bv" w
    | Coq.Init.Datatypes.list (stdpp.bitvector.definitions.bv ?n) =>
        let w := eval vm_compute in (Coq.ZArith.BinInt.Z.of_N n) in idtac "@@ZF B" H "list_bv" w
    | _ =>
        (* A type alias (`Definition DecodeItemOutcome := list byte`, `list EvmSailRlp...byte`) is
           classified by its normal form; an inductive with one constructor is a record (projected by
           project_records). *)
        let U := eval cbv in T in
        tryif constr_eq U T then
          tryif (is_ind T; assert_succeeds (
                   let zf_r := fresh "zf_r" in
                   assert (zf_r : T -> Coq.Init.Logic.True)
                     by (let zf_y := fresh "zf_y" in intro zf_y; destruct zf_y; [exact Coq.Init.Logic.I])))
          then idtac "@@ZF B" H "record" T
          else idtac "@@ZF B" H "other"
        else zf_kind H U
    end
  end.
Ltac zf_binders :=
  repeat lazymatch goal with
  | |- forall _ : ?T, _ => intro; lazymatch goal with H : _ |- _ => zf_kind H T end
  end;
  idtac "@@ZF E".
Ltac zf_decide P :=
  apply (stdpp.decidable.bool_decide_eq_true_1 P); vm_compute;
  lazymatch goal with
  | |- true = true => reflexivity
  | |- false = true => fail
  | _ => idtac "@@ZF stuck"; fail
  end.
(* The head constant of a fact. *)
Ltac zf_head P := lazymatch P with
  | ?f _ _ _ _ _ _ _ _ => f | ?f _ _ _ _ _ _ _ => f | ?f _ _ _ _ _ _ => f | ?f _ _ _ _ _ => f
  | ?f _ _ _ _ => f | ?f _ _ _ => f | ?f _ _ => f | ?f _ => f | ?f => f end.
(* Facts a real-state screen may take as holding (tools/oblig/normalise.py, binder map `assume`):
   none unless the screen redefines this tactic. *)
Ltac zf_assumable P := fail.
(* A fact without a Decision instance is tried once more at its head normal form
   (a marker definition around a decidable fact). *)
Ltac zf_holds :=
  lazymatch goal with |- ?P =>
    tryif zf_assumable P then (idtac "@@ZF assumed"; admit) else
    tryif (let _ := constr:(stdpp.decidable.bool_decide P) in idtac) then zf_decide P
    else (let Q := eval hnf in P in
          tryif (let _ := constr:(stdpp.decidable.bool_decide Q) in idtac)
          then (change Q; zf_decide Q) else (idtac "@@ZF nodec"; fail))
  end.
Ltac zf_props H :=
  lazymatch type of H with
  | forall _ : ?P, _ =>
      lazymatch type of P with
      | Prop => let Hp := fresh "zf_p" in
                assert (Hp : P) by zf_holds; specialize (H Hp); clear Hp; zf_props H
      | _ => idtac
      end
  | _ => idtac
  end.
Ltac zf_step H v := zf_props H; specialize (H v).
Ltac zf_finish H :=
  zf_props H; idtac "@@ZF concl";
  lazymatch type of H with ?C =>
    let Hn := fresh "zf_n" in assert (Hn : ~ C) by zf_holds; exact (Hn H) end.
"""


class FalsifyError(ValueError):
    pass


# ---- the goal ----

STATEMENT_LEMMA = re.compile(r"^Lemma (?P<name>\S+) :\n(?P<stmt>.*?)\.\nProof\.", re.S | re.M)
STATEMENT_GOAL = re.compile(r"^Goal (?P<stmt>.*)\.\s*$", re.S | re.M)


def read_goal(path, lemma=None):
    """Return (preamble text or None for a leftover goal, statement text, name)."""
    text = Path(path).read_text()
    if lemma:
        match = re.search(r"^Lemma %s :\n(?P<stmt>.*?)\.\nProof\." % re.escape(lemma), text, re.S | re.M)
        if not match:
            raise FalsifyError("%s: no lemma %s." % (path, lemma))
        header = [line for line in text[:match.start()].splitlines() if rl.rrm.HEADER_LINE.match(line)]
        return "\n".join(header) + "\n", match["stmt"].strip(), lemma
    match = STATEMENT_LEMMA.search(text)
    if match:
        return text[:match.start()], match["stmt"].strip(), match["name"]
    match = STATEMENT_GOAL.search(text)
    if match:
        return None, match["stmt"].strip(), Path(path).stem
    raise FalsifyError("%s: neither a Lemma with Proof. nor a Goal." % path)


QUALIFIED = re.compile(r"(?<![\w'.])([A-Za-z_][\w']*(?:\.[A-Za-z_][\w']*)+)")


def load_roots(args, coqlib):
    """(logical prefix, directory) pairs: the bank's -Q/-R pairs, the stdlib, user-contrib."""
    roots = []
    for i, arg in enumerate(args):
        if arg in ("-Q", "-R") and i + 2 < len(args):
            roots.append((args[i + 2], Path(args[i + 1])))
    if coqlib:
        roots.append(("Coq", Path(coqlib) / "theories"))
        contrib = Path(coqlib) / "user-contrib"
        if contrib.is_dir():
            roots += [(p.name, p) for p in contrib.iterdir() if p.is_dir()]
    return roots


def module_file(name, roots):
    for logical, directory in roots:
        if name == logical or not name.startswith(logical + "."):
            continue
        candidate = directory.joinpath(*name[len(logical) + 1:].split(".")).with_suffix(".vo")
        if candidate.exists():
            return candidate
    return None


def leftover_requires(statement, roots):
    """`Require` lines for the modules that the qualified names of STATEMENT live in."""
    modules = []
    for name in sorted(set(QUALIFIED.findall(statement))):
        parts = name.split(".")
        for cut in range(len(parts) - 1, 0, -1):
            module = ".".join(parts[:cut])
            if module_file(module, roots):
                if module not in modules:
                    modules.append(module)
                break
    return ["Require %s." % module for module in modules]


# ---- literals and values ----

POSITIVE = re.compile(r"\b(Zpos|Npos|Zneg)\b")


def parse_positive(text, i):
    """Parse a positive constructor term at TEXT[i:]; return (value, end) or None."""
    while i < len(text) and text[i] == " ":
        i += 1
    if text.startswith("xH", i):
        return 1, i + 2
    if text.startswith("(", i):
        inner = parse_positive(text, i + 1)
        if not inner:
            return None
        value, j = inner
        while j < len(text) and text[j] == " ":
            j += 1
        return (value, j + 1) if j < len(text) and text[j] == ")" else None
    for ctor, bit in (("xO", 0), ("xI", 1)):
        if text.startswith(ctor, i) and not text[i + 2:i + 3].isalnum():
            inner = parse_positive(text, i + 2)
            return (2 * inner[0] + bit, inner[1]) if inner else None
    return None


def literals(statement):
    """Integer literals of the statement: decimal, hex, positive constructor terms, unary nats."""
    found = {int(m) for m in re.findall(r"(?<![\w'.])(\d+)(?![\w'])", statement)}
    found |= {-int(m) for m in re.findall(r"\(-(\d+)\)", statement)}
    found |= {int(m, 16) for m in re.findall(r"\b0x([0-9a-fA-F]+)\b", statement)}
    for match in POSITIVE.finditer(statement):
        parsed = parse_positive(statement, match.end())
        if parsed:
            found.add(-parsed[0] if match[1] == "Zneg" else parsed[0])
    for run in re.findall(r"(?<![\w'])S (?:\(S )*O(?![\w'])", statement):
        found.add(1 + run.count("(S "))
    return found


def value_pool(statement):
    pool = {0, 1}
    for value in literals(statement):
        pool |= {value - 1, value, value + 1}
    for k in POWERS:
        pool |= {2 ** k - 1, 2 ** k}
    pool |= set(RAM_BOUNDS)
    return sorted(pool, key=lambda v: (abs(v), v))


def fits(kind, width, value):
    if kind == "Z":
        return True
    if kind == "nat":
        return 0 <= value <= NAT_MAX
    if kind == "N":
        return value >= 0
    if kind == "bv":
        return 0 <= value < 2 ** width
    if kind == "bool":
        return value in (0, 1)
    return False


def candidates(binder, pool):
    kind, width = binder["kind"], binder.get("width")
    if kind == "bytes":
        return [dict(bytes=n, fill=fill) for n in BYTE_LENGTHS for fill in ("zero", "ramp", "ff")]
    if kind == "bool":
        return [False, True]
    values = [v for v in pool if fits(kind, width, v)]
    if kind == "bv":
        values += [v % 2 ** width for v in pool if v < 0]
        values += [2 ** width - 1, 2 ** (width - 1)]
    out = []
    for v in values:
        if v not in out:
            out.append(v)
    return out


def coq_value(binder, value):
    kind, width = binder["kind"], binder.get("width")
    if kind == "Z":
        return "(%d)%%Z" % value
    if kind == "nat":
        return "(%d)%%nat" % value
    if kind == "N":
        return "(%d)%%N" % value
    if kind == "bool":
        return "true" if value else "false"
    if kind == "bv":
        return "(stdpp.bitvector.definitions.Z_to_bv (%d)%%N (%d)%%Z)" % (width, value % 2 ** width)
    if kind == "bytes" and "hex" in value:
        # The bytes of a machine-run snapshot (the screen of tools/oblig/normalise.py).
        return ("(Coq.Lists.List.map (fun z : Coq.Numbers.BinNums.Z => stdpp.bitvector.definitions.Z_to_bv (8)%%N z) %s)"
                % zlist(bytes.fromhex(value["hex"])))
    if kind == "bytes":
        n, fill = value["bytes"], value["fill"]
        if fill == "ramp":
            return ("(Coq.Lists.List.map (fun i : nat => stdpp.bitvector.definitions.Z_to_bv (8)%%N "
                    "(Coq.ZArith.BinInt.Z.of_nat i)) (Coq.Lists.List.seq 0 (%d)%%nat))" % n)
        byte = 255 if fill == "ff" else 0
        return "(Coq.Lists.List.repeat (stdpp.bitvector.definitions.Z_to_bv (8)%%N (%d)%%Z) (%d)%%nat)" % (byte, n)
    raise FalsifyError("No value form for kind %s." % kind)


def zlist(values):
    """A Rocq list of Z literals, written with cons and nil (no list notation needed)."""
    out = "(@Coq.Init.Datatypes.nil Coq.Numbers.BinNums.Z)"
    for v in reversed(list(values)):
        out = "(@Coq.Init.Datatypes.cons Coq.Numbers.BinNums.Z (%d)%%Z %s)" % (v, out)
    return out


def default_value(binder):
    return candidates(binder, [0])[0]


# ---- machine-run snapshots ----

def as_int(value):
    if isinstance(value, bool):
        return int(value)
    if isinstance(value, int):
        return value
    if isinstance(value, str):
        return int(value, 0)
    return None


def snapshot_values(path):
    """{register or argument name: int} of one STATE-<offset>.json (schema of tools/oblig/exec/run.py:
    `registers` maps x0..x31 or ABI names to integers or hex strings; `arguments`/`args`, when present,
    maps contract argument names to values)."""
    data = json.loads(Path(path).read_text())
    out = {}
    registers = data.get("registers") or data.get("regs") or {}
    if isinstance(registers, list):
        registers = {"x%d" % i: v for i, v in enumerate(registers)}
    for name, raw in registers.items():
        value = as_int(raw)
        if value is not None:
            out[ABI.get(name, name)] = value
    for key in ("arguments", "args"):
        for name, raw in (data.get(key) or {}).items():
            value = as_int(raw)
            if value is not None:
                out["arg:" + name] = value
    return out


def snapshots(exec_dir, offset):
    if not exec_dir or not offset:
        return []
    offset = offset.lower().removeprefix("0x").removeprefix("+")
    found = []
    for path in sorted(Path(exec_dir).glob("*/STATE-*.json")):
        stem = path.stem[len("STATE-"):].lower().removeprefix("0x").removeprefix("+")
        if stem == offset or stem.lstrip("0") == offset.lstrip("0"):
            found.append((path.parent.name, snapshot_values(path)))
    return found


def snapshot_assignment(binders, values):
    assignment, used = {}, False
    for b in binders:
        match = REGISTER.search(b["name"])
        register = ABI.get(match[1], match[1]) if match else None
        value = values.get(register) if register else None
        if value is None:
            value = values.get("arg:" + b["name"])
        if value is not None and b["kind"] in ("Z", "N", "nat", "bv"):
            if b["kind"] == "bv":
                value %= 2 ** b["width"]
            if fits(b["kind"], b.get("width"), value):
                assignment[b["name"]] = value
                used = True
                continue
        assignment[b["name"]] = default_value(b)
    return assignment if used else None


# ---- assignments ----

def assignments(binders, statement, snaps=(), limit=LIMIT):
    """The fixed, deterministic list of at most LIMIT assignments (dicts name -> value)."""
    data = [b for b in binders if b["kind"] != "prop"]
    pool = value_pool(statement)
    lists = {b["name"]: candidates(b, pool) for b in data}
    out, seen = [], set()

    def add(assignment, origin):
        key = json.dumps(assignment, sort_keys=True)
        if key not in seen and len(out) < limit:
            seen.add(key)
            out.append(dict(values=assignment, origin=origin))

    for input_id, values in snaps:
        snap = snapshot_assignment(data, values)
        if snap:
            add(snap, "snapshot:" + input_id)
    base = {b["name"]: default_value(b) for b in data}
    add(dict(base), "base")
    for v in pool:
        uniform = {}
        for b in data:
            choices = lists[b["name"]]
            if b["kind"] == "bytes":
                uniform[b["name"]] = choices[min(len(choices) - 1, pool.index(v) % len(choices))]
            elif b["kind"] == "bool":
                uniform[b["name"]] = bool(v % 2)
            elif b["kind"] == "bv":
                uniform[b["name"]] = v % 2 ** b["width"]
            else:
                uniform[b["name"]] = v if fits(b["kind"], None, v) else base[b["name"]]
        add(uniform, "uniform")
    single_budget = len(out) + (limit - len(out)) // 2
    for b in data:
        for value in lists[b["name"]]:
            if len(out) >= single_budget:
                break
            add(dict(base, **{b["name"]: value}), "single:" + b["name"])
    rng = random.Random(hashlib.sha256(statement.encode()).hexdigest())
    tries = 0
    while data and len(out) < limit and tries < 20 * limit:
        tries += 1
        add({b["name"]: rng.choice(lists[b["name"]]) for b in data}, "mixed")
    return out


def binder_term(binder, assignment):
    """The value of BINDER under ASSIGNMENT (leaf name -> value): a projected record is its constructor
    applied to its fields' values."""
    if binder["kind"] == "record" and "fields" in binder:
        return "(%s %s)" % (binder["ctor"], " ".join(binder_term(f, assignment) for f in binder["fields"]))
    return coq_value(binder, assignment[binder["name"]])


def steps(binders, assignment):
    calls = ["zf_step zf_H %s" % binder_term(b, assignment) for b in binders if b["kind"] != "prop"]
    return "; ".join(calls + ["zf_finish zf_H"])


# ---- Rocq files ----

def preamble(goal_preamble, statement, args, coqlib):
    if goal_preamble is None:
        requires = leftover_requires(statement, load_roots(args, coqlib))
        goal_preamble = "\n".join(requires) + "\n"
    return REQUIRES + goal_preamble.rstrip() + "\nLocal Open Scope Z_scope.\n" + LTAC


def statement_def(statement):
    return "\nDefinition zf_stmt : Prop :=\n  %s.\n" % statement


def probe_text(pre, statement):
    return pre + statement_def(statement) + "\nGoal zf_stmt.\nProof. unfold zf_stmt. zf_binders.\nAbort.\n"


def search_text(pre, statement, binders, rows):
    out = [pre, statement_def(statement)]
    for k, row in enumerate(rows):
        out.append("\nGoal ~ zf_stmt.\nProof. unfold zf_stmt; intro zf_H.\n"
                   "idtac \"@@ZF try %d\"; tryif (solve [%s]) then idtac \"@@ZF hit %d\" else idtac \"@@ZF miss %d\".\n"
                   "Abort.\n" % (k, steps(binders, row["values"]), k, k))
    return "".join(out)


def refute_text(pre, statement, binders, assignment):
    return (pre + statement_def(statement)
            + "\nLemma zf_refute : ~ zf_stmt.\nProof. unfold zf_stmt; intro zf_H. %s.\nQed.\n"
            "Print Assumptions zf_refute.\n" % steps(binders, assignment))


def records(log_text):
    """`@@ZF` lines of a compile log, timestamps removed."""
    out = []
    for line in log_text.split("\n"):
        line = rl.STAMP.sub(r"\2", line)
        if line.startswith("@@ZF "):
            out.append(line[5:].strip())
    return out


def parse_binders(lines):
    binders, ended = [], False
    for line in lines:
        if line == "E":
            ended = True
        elif line.startswith("B "):
            parts = line.split()
            name, kind = parts[1], parts[2]
            binder = dict(name=name, kind=kind)
            if kind == "record":
                binder["type"] = " ".join(parts[3:])
                binders.append(binder)
                continue
            width = int(re.sub(r"%Z$", "", parts[3])) if len(parts) > 3 else None
            if kind == "bv":
                binder["width"] = width
            elif kind == "list_bv":
                binder["kind"] = "bytes" if width == 8 else "other"
                if width != 8:
                    binder["type"] = "list (bv %d)" % width
            binders.append(binder)
    return binders, ended


# ---- record binders ----

RECORD_DECL = re.compile(r"^Record\s+(\w+)\s*(?::\s*Type\s*)?:=\s*(\w+)?\s*\{(.*?)\}\s*\.", re.S | re.M)


def field_binder(name, text):
    """The binder of a record field of type TEXT when its type is a checked kind, else None."""
    text = " ".join(text.split())
    if text in ("Z", "nat", "N", "bool"):
        return dict(name=name, kind=text)
    match = re.fullmatch(r"bv \(?(\d+)\)?", text)
    if match:
        return dict(name=name, kind="bv", width=int(match[1]))
    if text in ("list byte", "list (bv 8)"):
        return dict(name=name, kind="bytes")
    return None


def record_fields(source, name):
    """(constructor, [(field, type text)]) of `Record NAME` in the Rocq SOURCE text."""
    text = re.sub(r"\(\*.*?\*\)", " ", source, flags=re.S)
    for match in RECORD_DECL.finditer(text):
        if match[1] == name:
            fields = []
            for item in match[3].split(";"):
                names, _, kind = item.partition(":")
                fields += [(field, " ".join(kind.split())) for field in names.split()]
            return match[2] or "Build_" + name, fields
    raise FalsifyError("no `Record %s` in the source" % name)


def load_records(path=RECORDS_FILE):
    """{record type: dict(ctor, fields=[(field, type text)])} of the registry RECORDS_FILE: a row
    {type, source} takes its constructor and fields from the `Record` declaration in SOURCE (the
    constructor fully qualified by SOURCE's module path); a row {type, ctor, fields} gives them."""
    data = json.loads(Path(path).read_text())
    if data.get("schema") != "oblig-records/1":
        raise FalsifyError("%s: schema is not oblig-records/1" % path)
    out = {}
    for row in data["records"]:
        if "source" in row:
            ctor, fields = record_fields((ROOT / row["source"]).read_text(), row["type"])
            module = ".".join(Path(row["source"]).with_suffix("").parts)
            out[row["type"]] = dict(ctor="@%s.%s" % (module, ctor), fields=fields)
        else:
            out[row["type"]] = dict(ctor=row["ctor"], fields=[tuple(field) for field in row["fields"]])
    return out


def _projected(type_text, path, records, seen=()):
    """(record binder named PATH with its fields, None) or (None, why) for a record of type TYPE_TEXT."""
    short = type_text.rpartition(".")[2]
    entry = records.get(short)
    if entry is None or short in seen:
        return None, ""
    fields = []
    for field, text in entry["fields"]:
        name = "%s_%s" % (path, field) if path else field
        leaf = field_binder(name, text)
        if leaf is None:
            leaf, _ = _projected(text, name, records, seen + (short,))
            if leaf is None:
                return None, " (field %s : %s)" % (field, text)
        fields.append(leaf)
    return dict(name=path, kind="record", type=type_text, ctor=entry["ctor"], fields=fields), None


def project_records(binders, registry=None):
    """(BINDERS, reason): each `record` binder whose type the registry (load_records) lists, its fields
    checked kinds or registered records, gets `ctor` and `fields`: nested binders, each leaf named by its
    projection path (`keysBase_toOwnedList_arrayListLength`, the GENERALISE convention of
    tools/oblig/normalise.py), so the search instantiates the fields and builds the record. REASON is
    None, or `unscreened: record binder <name> : <type>` for a record binder that cannot be projected
    (or the leaf names that collide)."""
    registry = load_records() if registry is None else registry
    out, reason = [], None
    for binder in binders:
        if binder["kind"] != "record":
            out.append(binder)
            continue
        projected, why = _projected(binder["type"], "", registry)
        if projected is None:
            reason = reason or "unscreened: record binder %s : %s%s" % (binder["name"], binder["type"], why)
            out.append(binder)
        else:
            out.append(dict(binder, ctor=projected["ctor"], fields=projected["fields"]))
    names = [leaf["name"] for leaf in leaves(out)]
    clash = sorted({name for name in names if names.count(name) > 1})
    if clash and reason is None:
        reason = "unscreened: record fields collide with other binders: " + ", ".join(clash)
    return out, reason


def leaves(binders):
    """BINDERS with each projected record replaced by its leaf fields (in order)."""
    out = []
    for binder in binders:
        out += leaves(binder["fields"]) if binder["kind"] == "record" and "fields" in binder else [binder]
    return out


def search_outcomes(lines):
    """Per assignment index: hit, concl (premises held), nodec, stuck, assumed (a premise was taken as
    holding through the screen's `zf_assumable`)."""
    out, current = {}, None
    for line in lines:
        head, _, rest = line.partition(" ")
        if head == "try":
            current = int(rest)
            out[current] = dict(hit=False, concl=False, nodec=False, stuck=False, assumed=False)
        elif current is None:
            continue
        elif head == "hit":
            out[int(rest)]["hit"] = True
        elif head in ("concl", "nodec", "stuck", "assumed"):
            out[current][head] = True
    return out


# ---- the compile route ----

class Route:
    """Compiles with the bank's coqc arguments. By default each compile runs in its own
    resource-guard scope (the route of residual_loop.py). DIRECT runs coqc as a plain child
    under an address-space limit of DIRECT_GIB; the tool tests use it, because the guard
    refuses its live ledger to test processes, and their files load only stdpp."""

    def __init__(self, bank, ocamlpath=None, direct=False, claim=CLAIM):
        bank = Path(bank)
        raw = [a for a in json.loads((bank / "ARGS.json").read_text()) if a != "-time"]
        if "ZesuSsz" in raw:
            self.args, lib = rl.bank_args(bank)
        else:
            # Plain coqc arguments: pure goals over the standard library and stdpp only.
            self.args, lib = raw, ""
        self.ocamlpath = ocamlpath or lib
        self.direct = direct
        self.claim = claim
        self._coqlib = None

    @property
    def coqlib(self):
        if self._coqlib is None:
            proc = subprocess.run([self.args[0], "-where"], capture_output=True, text=True)
            self._coqlib = proc.stdout.strip() if proc.returncode == 0 else ""
        return self._coqlib

    def compile(self, path, tag):
        if self.direct:
            return self.compile_direct(Path(path))
        result = rl.scoped(path, tag, self.args, self.ocamlpath, claim=self.claim)
        text = Path(result["log"]).read_text(errors="replace")
        return result, text

    def compile_direct(self, path):
        limit = DIRECT_GIB << 30
        proc = subprocess.run(self.args + [path.name], cwd=path.parent, capture_output=True, text=True,
                              env=rl.clean_env(dict(OCAMLPATH=self.ocamlpath)),
                              preexec_fn=lambda: resource.setrlimit(resource.RLIMIT_AS, (limit, limit)))
        text = "".join("0.000 %s\n" % line for line in (proc.stdout + proc.stderr).split("\n"))
        path.with_suffix(".log").write_text(text)
        for suffix in (".vo", ".vok", ".vos", ".glob"):
            path.with_suffix(suffix).unlink(missing_ok=True)
        (path.parent / ("." + path.stem + ".aux")).unlink(missing_ok=True)
        return dict(returncode=proc.returncode, log=str(path.with_suffix(".log"))), text


def compile_error(text):
    return rl.errors_of(text, limit=20)


def first_error(text):
    """The message of the first `Error:` of a compile log, on one line."""
    lines = [rl.STAMP.sub(r"\2", line) for line in text.split("\n")]
    for i, line in enumerate(lines):
        if line.startswith("Error:"):
            rest = [line[len("Error:"):]] + [l for l in lines[i + 1:i + 4] if l.strip() and not l.startswith("@@")]
            return " ".join(part.strip() for part in rest).strip()
    rest = [line.strip() for line in lines if line.strip() and not line.startswith("@@CPU")]
    return " ".join(rest[-2:]) if rest else "no output"


def check(goal, route, out=None, lemma=None, exec_dir=None, offset=None, limit=LIMIT, registry=None):
    goal = Path(goal)
    out = Path(out) if out else goal.parent
    out.mkdir(parents=True, exist_ok=True)
    goal_preamble, statement, name = read_goal(goal, lemma)
    tag = "falsify-" + hashlib.sha256(statement.encode()).hexdigest()[:12]
    pre = preamble(goal_preamble, statement, route.args, route.coqlib)
    report = dict(goal=str(goal), lemma=name, statement_sha256=hashlib.sha256(statement.encode()).hexdigest())

    (out / "probe.v").write_text(probe_text(pre, statement))
    result, text = route.compile(out / "probe.v", tag + "-probe")
    binders, ended = parse_binders(records(text))
    report["binders"] = binders
    if result["returncode"] != 0 or not ended:
        report.update(verdict="unchecked", reason="probe failed: " + first_error(text), error=compile_error(text))
        return finish(out, report)
    binders, unscreened = project_records(binders, registry)
    report["binders"] = binders
    if unscreened:
        report.update(verdict="unchecked", reason=unscreened)
        return finish(out, report)
    other = [b for b in leaves(binders) if b["kind"] not in CHECKED_KINDS]
    if other:
        report.update(verdict="unchecked", reason="binder type outside Z, nat, N, bv n, list byte, bool: %s"
                      % ", ".join(b["name"] for b in other))
        return finish(out, report)

    rows = assignments(leaves(binders), statement, snapshots(exec_dir, offset), limit)
    (out / "search.v").write_text(search_text(pre, statement, binders, rows))
    result, text = route.compile(out / "search.v", tag + "-search")
    outcomes = search_outcomes(records(text))
    report.update(assignments=len(rows), tried=len(outcomes),
                  conclusion_tested=sum(1 for o in outcomes.values() if o["concl"]),
                  nodec=sum(1 for o in outcomes.values() if o["nodec"]),
                  stuck=sum(1 for o in outcomes.values() if o["stuck"]))
    if result["returncode"] != 0 or len(outcomes) != len(rows):
        report.update(verdict="unchecked", reason="search compile failed", error=compile_error(text))
        return finish(out, report)
    hits = sorted(k for k, o in outcomes.items() if o["hit"])
    if not hits:
        decided = [o for o in outcomes.values() if not (o["nodec"] or o["stuck"])]
        if not decided:
            report.update(verdict="unchecked", reason="no assignment could be decided "
                          "(a fact has no Decision instance or does not reduce)")
        else:
            report.update(verdict="passed")
            if not report["conclusion_tested"]:
                report["reason"] = "no assignment satisfied the premises; the conclusion was never decided"
        return finish(out, report)

    k = hits[0]
    assignment = rows[k]
    (out / "refute.v").write_text(refute_text(pre, statement, binders, assignment["values"]))
    result, text = route.compile(out / "refute.v", tag + "-refute")
    assumptions = "\n".join(rl.STAMP.sub(r"\2", line) for line in text.split("\n")
                            if "Closed under the global context" in line or "Axioms:" in line)
    report["hit"] = dict(index=k, origin=assignment["origin"], assignment=assignment["values"],
                         refute=str(out / "refute.v"))
    if result["returncode"] != 0:
        report.update(verdict="unchecked", reason="the kernel check of the hit failed", error=compile_error(text))
        return finish(out, report)
    report.update(verdict="false", kernel=dict(returncode=0, assumptions=assumptions.strip()))
    return finish(out, report)


def finish(out, report):
    rl.write_json(Path(out) / "FALSIFY.json", report)
    return report


def summary(report):
    line = "FALSIFY %s %s" % (report["verdict"], report.get("lemma", ""))
    if "tried" in report:
        line += " tried=%d conclusion_tested=%d" % (report["tried"], report["conclusion_tested"])
    if report.get("hit") and report["verdict"] == "false":
        line += " assignment=%s" % json.dumps(report["hit"]["assignment"], sort_keys=True)
    if report.get("reason"):
        line += " reason=%s" % report["reason"]
    return line


def main(argv=None):
    ap = argparse.ArgumentParser(description=__doc__.split("\n\n")[0])
    sub = ap.add_subparsers(dest="command", required=True)
    c = sub.add_parser("check")
    c.add_argument("goal")
    c.add_argument("--bank", required=True, help="bank dir with ARGS.json (as residual_loop.py export)")
    c.add_argument("--ocamlpath", help="findlib dir with the zesu-signature-gates plugin (default: the bank's)")
    c.add_argument("--lemma", help="lemma of a rendered residual module")
    c.add_argument("--out")
    c.add_argument("--exec-dir", help="RUN/exec of tools/oblig/exec/run.py")
    c.add_argument("--offset", help="4-hex offset of the goal's block (selects STATE-<offset>.json)")
    c.add_argument("--limit", type=int, default=LIMIT)
    a = ap.parse_args(argv)
    if not 0 < a.limit <= LIMIT:
        ap.error("--limit must be between 1 and %d" % LIMIT)
    try:
        report = check(a.goal, Route(a.bank, a.ocamlpath), a.out, a.lemma, a.exec_dir, a.offset, a.limit)
    except FalsifyError as error:
        sys.exit("falsify: %s" % error)
    print(summary(report))


if __name__ == "__main__":
    main()
