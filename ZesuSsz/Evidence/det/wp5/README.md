# WP5: generated segment modules

`tools/det/gen_segment.py` writes a segment module from its interface:
the binders and boundary predicates the segment already states, the code
premise in the shape the automation can use, and

```
Proof. move => *. zesu_block. Qed.
```

No proof line is written by hand, by construction. The generated modules
live here rather than under `ZesuSsz/Proofs/`, because a module that does
not close belongs nowhere near `check-iris`: `--compile` copies one into
the theory for the length of its build and removes it again.

## Result

| segment | hand lines before | after | closes | stall |
|---|---|---|---|---|
| tail fields 3 | 19 | 0 | no | C2 `subsume ↦ₘ∗ ↦ₘ∗` |
| suffix entry | 28 | 0 | no | C3 `subsume (…) (…)` |
| post transactions | 34 | 0 | no | C8 `∗[11] match ∗ ↦ₘ∗ ∗ (…)` |
| epilogue | 14 | 0 | no | C4 `∃ : isla_trace` |
| total | 95 | 0 | 0 of 4 | |

The acceptance -- four of four regenerating and compiling with no hand
line -- is not met. What the generator removes today is the *shape* of
the work: the imports, the binders, the code premise and the proof body
are derived, and each segment's remaining debt is one named residual
rather than nineteen to thirty-four lines of bespoke Rocq.

## One change the generator makes for free

Every generated module states its code premise as

```
instr_lookup_resources IslaTraces.write_success_blocks.Index.lookup -∗
IslaTraces.write_success_blocks.Index.spec_instr_resources -∗
```

instead of the folded `writeSuccessCompleteNativeCode`. Islaris already
resolves an instruction fetch from the first of those
(`InstrSpecs/Lookup.v`); it simply cannot see the resource inside a
bundle. That is the corpus's largest single gap -- 122 proofs, 888 hand
lines, backlog rank 1 -- and a generated module never has it.

## The four tickets

Each is the first goal the automation cannot take, for one segment, with
the C1 rule installed and C2 compiled in:

1. **C2, tail fields 3.** The rule exists (`Automation/WordArrayBytes.v`)
   and clears this stall. It is not exported because the merged proof
   then needs a representation equation between the boundary's *name* for
   the bytes and the bytes the block holds. A generated module states the
   boundary as the bytes the block holds, so it is the caller this rule
   was waiting for -- once the boundary itself is generated (WP4).
2. **C3, suffix entry.** `subsume` against a sealed predicate: the exit
   wants a closed contract's return shape and the automation holds its
   parts.
3. **C8, post transactions.** A frame handoff of eleven conjuncts with a
   bare `match` on a spec field.
4. **C4, epilogue.** `∃ : isla_trace`: the block asks for an instruction
   trace where the spec table should supply it. Note that
   `InstrSpecs/Lookup.v` defines
   `find_in_context_instr_body_lookup_resources_inst` and never registers
   it, so `spec_instr_resources` is dead weight for the search.
   Registering it fires and takes the frame from 47 to 8, but it also
   unifies the lemma's own entry address with the wrong table row; it
   needs a guard excluding the goal's own entry.

## Reproduce

```
python3 tools/det/gen_segment.py --set ZesuSsz/Evidence/det/boundary_set.txt \
  --extra-import ZesuSsz.Automation.WordArrayBytes --compile \
  --report ZesuSsz/Evidence/det/wp5/generated.jsonl
python3 tools/det/handlines.py --set ZesuSsz/Evidence/det/boundary_set.txt \
  --before ccf505e8 --after HEAD
```
