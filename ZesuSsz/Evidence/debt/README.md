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
