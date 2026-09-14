Require Export ZesuSsz.Automation.ArrayDynamicCursors.
Require Export ZesuSsz.Automation.ArrayDynamicDestination.
Require Export ZesuSsz.Automation.ArrayDynamicBounds.
Require Export ZesuSsz.Automation.ArrayCounterBounds.
Require Export ZesuSsz.Automation.ArrayCounterStep.
Require Export ZesuSsz.Automation.ArrayCopyComplete.
Require Export ZesuSsz.Automation.ArrayCopyStep.
Require Export ZesuSsz.Automation.TraceResume.
Require Import isla.riscv64.riscv64.

Ltac zesu_copy_normalize_destination_index :=
  match goal with
  | Hle : (bv_unsigned ?offset <= bv_unsigned ?limit)%Z,
    Hlow : (?minimum <= bv_unsigned ?row)%Z,
    Hhigh : (bv_unsigned ?row + bv_unsigned ?limit < ?maximum)%Z
    |- context[bv_unsigned (bv_add ?row ?offset) - bv_unsigned ?row] =>
    zesu_require_machine_ram_bounds minimum maximum;
    let Hindex := fresh "HcopyDestinationIndex" in
    assert (Hindex : bv_unsigned (row + offset)%bv - bv_unsigned row = bv_unsigned offset) by
      (clear -Hle Hlow Hhigh; bv_solve);
    rewrite Hindex; clear Hindex
  end.
Ltac zesu_copy_finish :=
  try rewrite !Z.add_0_r;
  repeat match goal with
  | Hlookup : _ !! Z.to_nat ((bv_unsigned _ + 0 - _) `div` 1) = Some _ |- _ =>
    rewrite Z.add_0_r in Hlookup
  end;
  try zesu_copy_normalize_destination_index;
  try (eapply array_cursor_dynamic_index_lt; eassumption);
  try (eapply array_copy_complete; eassumption);
  try zesu_resume;
  try (eapply array_counter_index_lt; eassumption);
  try zesu_resume;
  try rewrite length_insert; try assumption;
  try (eapply array_counter_next_le; eassumption);
  try (eapply array_copy_step; eassumption).
