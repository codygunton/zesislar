# Proof starting point

## Read these files first

1. `ZesuSsz/Contracts/Level1.v`: the generic interface.
   It defines `IslarisContractResources` and `IslarisContractCorrect`.
2. `ZesuSsz/Contracts/RlpDecodeItemContract.v`: the rung-1 arguments, outcomes, and resources.
   It defines `DecodeMeaningModuloKnownBugs`.
3. `ZesuSsz/Contracts/DecodeItemSelected.v`: the exact rung-1 target on the selected code.
4. `ZesuSsz/Compliance/KnownBugs.v`: the one permitted divergence, `RlpLongLengthWrap`.
5. `ZesuSsz/Compliance/SailRun.v`: the evaluator for the concrete Sail decoder.
6. `Scaffolding/DecodeItemComplianceStatement.v`: the theorem to prove.
   This file is outside the production imports.

## Proof order

1. Prove the blocks with `zesu_block`.
   The chain driver in `tools/block/` runs each block from its entry state (`make block-run`).
2. Prove the byte-fold loop invariants.
   Use `ZesuSsz/Contracts/RlpDecodeItemByteFold.v` and `ZesuSsz/Automation/ByteFold.v`.
3. Prove the representation lemmas for each success and error path.
   Use `ZesuSsz/Contracts/ResultImage.v`.
4. Compose the Level 1 contract through `block_table_complete`.
   This lemma is in `ZesuSsz/Automation/BlockTable.v`.
5. Prove compliance through `DecodeMeaningModuloKnownBugs`.

Start every proof module with `Require Import ZesuSsz.Automation.All.`

## Rules

- Do not write an operational lemma per instruction.
- Do not write a `//@spec:` for a load or store from an array.
- Put Lithium hooks only in `ZesuSsz/Automation/Hooks.v`.
- A proof module must stay below 300 seconds and 6 GiB.
- Any other module must stay below 60 seconds and 2 GiB.
- More than five `iRename select` calls show a missing rule.
- More than forty lines per `instr_body` handoff show a missing rule.
- Report a missing rule to the lead. Fix it in `ZesuSsz/Automation/`.
- Test one lemma with `tools/coqc_scratch.sh`, not with a full module build.

## Current state

The baseline block pass reached zero of the 24 blocks.
One entry stall occurs at the instruction lookup.
A fix for this stall is in progress.

`docs/TRUST.md` states the trust boundary.
`docs/ai/plan/PLAN_STOCK_LADDER.md` section 5.2 describes the rung-1 work.
