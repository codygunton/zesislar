# Tech-debt sweep scripts

Read-only scripts behind `docs/ai/plan/TECH_DEBT_INVENTORY.md` and
`TECH_DEBT_PROPOSAL.md` (plan `PLAN_TECH_DEBT_SWEEP.md`). They read a
checkout of the root, the Dune traces of all worktrees, git, and the plans.
They write nothing into the tree. `run.sh` runs them in order.

| script | reads | writes |
|---|---|---|
| `gate_cost.py` | `trace.csexp` of every build dir | per-module wall s, CPU s, peak RSS |
| `inventory.py` | coqdep output, tree, cost, plans | one record per module, with class |
| `answers.py` | records, coqdep output | questions 1 to 5 |
| `script_refs.py` | tree, Makefile, dune, plans, git | question 6 |
| `branches.py` | git, `.worktrees/` | question 7 |
| `closed_cleanup_gap.py` | corpus at `14c42a48`, tree | question 8 |
| `render.py` | all of the above | the inventory |
| `proposal.py` | records, answers | the proposal |

`csexp.py` reads Dune's canonical s-expressions. The trace files hold
the environment of each build; the scripts never read it out.

    ZesuSsz/Evidence/debt/run.sh <root-sha> <out-dir>

## Pre-deletion step (sweep plan section 7, step 1)

| script | does |
|---|---|
| `tier_lists.py` | writes `tier1_remove_now.txt` and `carve_outs.txt` from one inventory run |
| `refreeze.py` | keeps set rows whose module imports `Automation.All` and survives tier 1; writes `benchmark_set_segments.txt` |
| `baseline_arms.sh` | v1 and v2 arms on both sets, then the three open segments, all under the guard |

The arms need the classifier-v2 and re-probe version of `benchmark.py`,
which only `origin/determinism` carries:

    git archive origin/determinism tools | tar -x -C <dir>
    ZesuSsz/Evidence/debt/baseline_arms.sh <root-sha> <dir>/tools

The worktree must hold `generated/isla-traces` and `build/`, which the arm
tree copies in.
