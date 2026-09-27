# Approved tier-1 removal

The source commit is `1bd760f5db927ef08ccbfb883410992b6c4b2bf5`.
The pre-deletion root is `214a47663d2d288127f75b3fd950bba4cc6afea9`.

The sweep removes 807 modules and 13 unused scripts.
It retains 48 carve-outs and the decoder examples required by the gate.
The source diff adds 102 lines and removes 80,507 lines.
The removed modules contain 73,507 lines.
The sweep removes three Dune exclusions.

Approval #87 moves four unchanged Local instances into their defining module.
The shape checker collected registrations globally from unrelated files.
Approval #97 retains the decoder examples and their original baseline entry.
The inventory omitted the gate's direct shell dependency on that module.
Neither repair changes a theorem statement or an automation rule.

The full preview passes at 24 jobs with zero timeouts.
Its compilation takes 292.782 seconds and reuses the shared build cache.
The focused baseline takes 1,617.246 seconds.
That baseline is not a full gate.
These measurements do not establish a cold-gate speedup.

All seven named assumption results match before and after.
The contract, main results, and three adequacy results are closed.
`zesuCompliance` retains its existing self axiom.
This sweep does not establish compliance or CP3.
The complete assumption output is stored with this report.

The cleanup follows the coordinator's reconciled name lists.
Remote references and branches with unique work remain.
The cleanup receipts record the actual removals and disk result.

The cleanup removes nine worktrees and 45 local branches.
The registered count decreases from 28 to 19.
Root then removes the completed audit worktree, leaving 18.
The recorded cleanup frees 11.60 GiB.
The final builder worktree removal occurs after this evidence commit.
