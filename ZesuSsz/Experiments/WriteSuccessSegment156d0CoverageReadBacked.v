Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Contracts.InstructionBoundary.
Require Import ZesuSsz.Experiments.WriteSuccessCoverageAutomation.
Require Import ZesuSsz.Experiments.WriteSuccessSegment15694.
Require Import ZesuSsz.Experiments.WriteSuccessSegment156d0.
Require Import ZesuSsz.Experiments.WriteSuccessSegment156d0ReadCoverage.

Lemma segment_156d0_read_backed_covered regs global mstatusBits address satp
    declared actual prefix26 done labels spawned after :
  read_mem global.(seq_mem) (bv_unsigned (writeSuccess156d0Address address)) 8 =
    Some (bv_to_bvn actual) ->
  IslaInstructionPrefixPath (writeSuccess15694Local
    (writeSuccess156d0Trace26 mstatusBits address satp declared) regs, global)
    prefix26 done -> done.1.(seq_trace) = tnil ->
  seq_step done.1 done.2 labels after.1 after.2 spawned ->
  declared = actual /\ exists prefix27,
  IslaInstructionPrefixPath (writeSuccess15694Local
    (writeSuccess156d0Trace27 mstatusBits address satp actual) regs, global)
    prefix27 done /\
  prefix26 = writeSuccess15694Observation (writeSuccess15694Local
    (writeSuccess156d0Trace27 mstatusBits address satp actual) regs) global :: prefix27.
Proof.
  intros Hmem Hprefix Hnil Hdone. have HdoneNb := seqStepSourceBlocking _ _ _ _ _ _ Hdone.
  destruct (writeSuccess15694TakeStep _ _ _ Hprefix ltac:(cbn; discriminate) Hnil HdoneNb)
    as (? & l27 & g27 & ? & p27 & Ho26 & Hs26 & Hnb27 & Hp27).
  eapply writeSuccess156d0ReadBackedValueCovered in Hs26.
  2: reflexivity. 2: exact Hmem. 2: exact Hnb27.
  destruct Hs26 as (-> & -> & -> & -> & ->).
  split; first reflexivity. exists p27. split; first exact Hp27.
  rewrite Ho26. reflexivity.
Qed.

Print Assumptions segment_156d0_read_backed_covered.
