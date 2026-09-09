Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Contracts.InstructionBoundary.
Require Import ZesuSsz.Experiments.WriteSuccessCoverageAutomation.
Require Import ZesuSsz.Experiments.WriteSuccessSegment15694.
Require Import ZesuSsz.Experiments.WriteSuccessSegment156d0.
Lemma segment_156d0_post_pc_covered regs global mstatusBits address satp value
    prefix29 done labels spawned after :
  regs !! "PC" = Some (RVal_Bits (Z_to_bv 64 0x156d0)) ->
  IslaInstructionPrefixPath (writeSuccess15694Local
    (writeSuccess156d0Trace29 mstatusBits address satp value)
    (<["x10" := RVal_Bits value]> regs), global) prefix29 done ->
  done.1.(seq_trace) = tnil -> seq_step done.1 done.2 labels after.1 after.2 spawned ->
  exists prefix30, IslaInstructionPrefixPath (writeSuccess15694Local
    (writeSuccess156d0Trace30 mstatusBits address satp value)
    (writeSuccess156d0Regs regs value), global) prefix30 done /\
  prefix29 = writeSuccess15694Observation (writeSuccess15694Local
    (writeSuccess156d0Trace30 mstatusBits address satp value)
    (writeSuccess156d0Regs regs value)) global :: prefix30.
Proof.
  intros Hpc Hprefix Hnil Hdone. have HdoneNb := seqStepSourceBlocking _ _ _ _ _ _ Hdone.
  destruct (writeSuccess15694TakeStep _ _ _ Hprefix ltac:(cbn; discriminate) Hnil HdoneNb)
    as (? & l30 & g30 & ? & p30 & Ho29 & Hs29 & ? & Hp30).
  eapply writeSuccessWriteRegCovered in Hs29.
  2: reflexivity. 2: { rewrite lookup_insert_ne; last congruence. exact Hpc. }
  2: reflexivity. 2: reflexivity.
  destruct Hs29 as (-> & -> & -> & ->). exists p30. split; first exact Hp30.
  rewrite Ho29. reflexivity.
Qed.
Print Assumptions segment_156d0_post_pc_covered.
