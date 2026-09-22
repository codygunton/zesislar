#!/usr/bin/env python3
"""Row 2: infer the trace a segment's boundary should state.

A block that calls out, or writes to MMIO, must show its events are
included in the trace its boundary declares. Two things go wrong today
and both are the boundary's fault, not the block's:

- the boundary declares a bare variable, so the inclusion carries no
  information and nothing can close it;
- the boundary declares a folded project definition whose descriptor
  list is `drop (length … + …) (map …)` over abstract fields, so no
  reduction reaches the write at its head.

Stating the trace as a Coq evar and letting the automation fill it in
does not work: an evar inside `spec_trace` sits in the context the
register search reads, and `FindHypEqual` is then postponed instead of
resolved. Measured, not assumed.

So the trace is inferred one event at a time, and stays concrete the
whole way. Start with a bare variable. The block stops at the first
inclusion and the goal names the event: `E x.1ₗ ⊆ tail`. Put `E tail`
in the boundary instead of `tail` and probe again; the block gets past
that call and stops at the next. After as many rounds as the segment
makes calls, the boundary states exactly the events the block emits and
every inclusion closes by reflexivity.

What comes out is the trace half of the segment's boundary, and at a
chain end it is also the statement of the equivalence lemma that meets
the frozen predicate.
"""

from __future__ import annotations

import argparse
import json
import re
import subprocess
import sys
from pathlib import Path

HERE = Path(__file__).resolve().parent

# `⌜<events> x.1ₗ ⊆ <declared>⌝`: the inclusion the block raises at a
# handover. The hole is always the first component of the `li_prod`.
INCLUSION = re.compile(r"⌜(?P<events>.+?)\s+(?P<hole>x\.1ₗ)\s+⊆\s+(?P<declared>.+?)⌝",
                       re.S)
# Coq's verdict when the inferred event mentions something the segment
# does not bind. The block emits its events in terms of what it holds at
# the stall, and some of that is a value it loaded, which Coq named
# locally: `vmem` and friends. Such an event is real and the boundary
# still cannot state it, so the round is a ticket, not an error.
UNBOUND = re.compile(r"The reference (?P<name>[A-Za-z_][A-Za-z0-9_']*) "
                     r"was not found")
# The other half of the same story. Where a call asks for an inclusion,
# a handover to the next boundary asks for the trace resource itself,
# with the continuation left as the hole: `spec_trace (E x.1ₗ)`. The
# event to add to the boundary is the same either way.
HANDOVER = re.compile(r"spec_trace\s*\(\s*(?P<events>.+?)\s+x\.1ₗ\s*\)", re.S)


def defining_lookup(context: str, name: str) -> str | None:
    """`name` written in terms the boundary can state, or None.

    A block names the word it loaded, and the same context carries the
    hypothesis that says where the word came from:

        Hlookup : take 69 (writeSuccessValues witness)
                    !! Z.to_nat (…) = Some vmem

    Everything on the left is bound by the segment, so the boundary can
    state the value as the project already states its siblings, with
    `default (BV 64 0) (… !! …)`. `WriteSuccessExactTailWithdrawalCountEntry.v`
    writes exactly that for indices 11 and 12 of this list.
    """
    pattern = re.compile(
        r"!!\s*(?P<index>.+?)\s*=\s*Some\s+" + re.escape(name) + r"\s*$")
    for line in (context or "").split("\n"):
        found = pattern.search(line.strip())
        if not found:
            continue
        head = line.strip()[:found.start()]
        # Drop the hypothesis name, keep the list expression.
        listing = head.split(":", 1)[1] if ":" in head.split("!!")[0] else head
        listing = listing.strip()
        if not listing:
            continue
        return f"default (BV 64 0) ({listing} !! {found['index'].strip()})"
    return None


def probe(spec: dict, out: Path, build_dir: Path, rule: Path | None,
          alternatives: list[str], seconds: int) -> dict:
    spec_file = out.with_suffix(".spec.json")
    spec_file.write_text(json.dumps([spec], indent=2) + "\n")
    command = [sys.executable, str(HERE / "infer_boundary.py"),
               "--specs", str(spec_file), "--out", str(out),
               "--build-dir", str(build_dir), "--seconds", str(seconds)]
    if rule:
        command += ["--rule", str(rule)]
    for alternative in alternatives:
        command += ["--alt", alternative]
    subprocess.run(command, check=False)
    text = out.read_text().strip()
    return json.loads(text.split("\n")[-1]) if text else {"outcome": "error"}


def next_event(conclusion: str, declared: str) -> str | None:
    """The events the stalled inclusion asks for, with the hole freed.

    Returns `<events> {tail}`, a format string, or None when the goal is
    not an inclusion against the trace this round declared.
    """
    match = INCLUSION.search(conclusion or "")
    if match is not None and match.group("declared").strip() != declared.strip():
        match = None
    if match is None:
        match = HANDOVER.search(conclusion or "")
    if match is None:
        return None
    events = " ".join(match.group("events").split())
    # The printed term is an application; it needs its own brackets
    # before it is substituted into an argument position.
    return "(" + events + " {tail})"


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--specs", type=Path, required=True)
    parser.add_argument("--trace-binder", default="tail",
                        help="the binder the boundary's trace is stated as")
    parser.add_argument("--rounds", type=int, default=12)
    parser.add_argument("--build-dir", type=Path,
                        default=Path("_build/agents/det"))
    parser.add_argument("--rule", type=Path, default=None)
    parser.add_argument("--alt", action="append", default=[])
    parser.add_argument("--seconds", type=int, default=1800)
    parser.add_argument("--out", type=Path, required=True)
    arguments = parser.parse_args()

    results = []
    for spec in json.loads(arguments.specs.read_text()):
        binder = arguments.trace_binder
        original = spec.get("infer_trace") or binder
        # A segment whose boundary declares a folded project definition
        # has no trace binder to grow. Give it one: the inferred trace
        # ends in a free tail, and at a chain end that tail is what the
        # equivalence lemma quantifies over.
        if f"({binder} : spec)" not in spec["binders"]:
            spec = dict(spec,
                        binders=f"{spec['binders']} ({binder} : spec)")
        # The boundary starts with a bare tail and grows one event a round.
        prefix = "{tail}"
        events: list[str] = []
        record: dict = {}
        context = ""
        for round_number in range(arguments.rounds):
            declared = prefix.format(tail=binder)
            attempt = dict(spec)
            attempt.pop("infer_trace", None)
            attempt["spec"] = spec["spec"].replace(original, declared)
            attempt["name"] = f"{spec['name']}_trace{round_number}"
            record = probe(attempt, arguments.out.with_suffix(
                f".{spec['name']}.{round_number}.jsonl"),
                arguments.build_dir, arguments.rule, arguments.alt,
                arguments.seconds)
            print(f"{spec['name']} round {round_number}: "
                  f"{record.get('outcome')} frame {record.get('frame')} "
                  f"{record.get('signature', '')}", flush=True)
            if record.get("outcome") == "reached":
                break
            context = record.get("context") or context
            unbound = sorted({match["name"] for line in
                              record.get("error_lines", [])
                              for match in [UNBOUND.search(line)] if match})
            if unbound:
                # The previous round read a real event off the goal and
                # this round says the boundary cannot state it. Before
                # giving up, look the name up where the block defined
                # it: a loaded word comes with the hypothesis that says
                # which element of which list it is, and every part of
                # that is bound by the segment.
                rewritten = prefix
                resolved = []
                for name in unbound:
                    definition = defining_lookup(context, name)
                    if definition is None:
                        continue
                    rewritten = re.sub(rf"\b{re.escape(name)}\b",
                                       f"({definition})", rewritten)
                    resolved.append(name)
                if resolved:
                    print(f"  {', '.join(resolved)} is a lookup the block "
                          f"already has; stating it in the boundary's own "
                          f"terms and retrying", flush=True)
                    prefix = rewritten
                    if events:
                        last = events[-1]
                        for name in resolved:
                            last = re.sub(
                                rf"\b{re.escape(name)}\b",
                                f"({defining_lookup(context, name)})", last)
                        events[-1] = last
                    continue
                print(f"  the event mentions {', '.join(unbound)}, which "
                      f"the segment does not bind and the context does "
                      f"not define: the boundary has to say where that "
                      f"value comes from", flush=True)
                break
            event = next_event(record.get("conclusion", ""), declared)
            if event is None:
                print("  not an inclusion against this round's trace; "
                      "the stall is a different ticket", flush=True)
                break
            if events and event == events[-1]:
                # The same event twice means the round did not get past
                # the call it just described, and the loop would grow
                # the boundary for ever. Stop and report it.
                print("  the same event twice; the round made no progress",
                      flush=True)
                break
            events.append(event)
            prefix = prefix.format(tail=event)
        results.append({"lemma": spec["name"], "rounds": len(events),
                        "events": events,
                        "unbound": sorted({
                            match["name"] for line in
                            record.get("error_lines", [])
                            for match in [UNBOUND.search(line)] if match}),
                        "outcome": record.get("outcome"),
                        "frame": record.get("frame"),
                        "pred_class": record.get("pred_class"),
                        "signature": record.get("signature"),
                        "inferred_trace": prefix.format(tail=binder)})
    arguments.out.write_text(
        "".join(json.dumps(r) + "\n" for r in results))
    for row in results:
        print(f"{row['lemma']}: {row['rounds']} events inferred, "
              f"{row['outcome']}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
