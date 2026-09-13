Require Export ZesuSsz.Automation.ArrayDynamicCursors.
Require Export ZesuSsz.Automation.ArrayDynamicDestination.
Require Export ZesuSsz.Automation.ArrayDynamicBounds.
Require Export ZesuSsz.Automation.ArrayCounterBounds.
Require Export ZesuSsz.Automation.ArrayCounterStep.
Require Export ZesuSsz.Automation.ArrayCopyComplete.
Require Export ZesuSsz.Automation.ArrayCopyStep.
Require Export ZesuSsz.Automation.TraceResume.
Require Import isla.riscv64.riscv64.

Ltac zesu_copy_finish :=
  try (eapply array_cursor_dynamic_index_lt; eassumption);
  try (eapply array_copy_complete; eassumption);
  try zesu_resume;
  try (eapply array_counter_index_lt; eassumption);
  try zesu_resume;
  try rewrite length_insert; try assumption;
  try (eapply array_counter_next_le; eassumption);
  try (eapply array_copy_step; eassumption).
