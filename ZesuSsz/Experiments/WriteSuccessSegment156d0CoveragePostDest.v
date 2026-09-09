Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Contracts.InstructionBoundary.
Require Import ZesuSsz.Experiments.WriteSuccessCoverageAutomation.
Require Import ZesuSsz.Experiments.WriteSuccessSegment15694.
Require Import ZesuSsz.Experiments.WriteSuccessSegment156d0.
Lemma segment_156d0_post_dest_covered regs global mstatusBits address satp value oldDest
    prefix28 done labels spawned after :
  regs !! "x10" = Some (RVal_Bits oldDest) ->
  IslaInstructionPrefixPath (writeSuccess15694Local
    (writeSuccess156d0Trace28 mstatusBits address satp value) regs, global)
    prefix28 done -> done.1.(seq_trace) = tnil ->
  seq_step done.1 done.2 labels after.1 after.2 spawned ->
  exists prefix29, IslaInstructionPrefixPath (writeSuccess15694Local
    (writeSuccess156d0Trace29 mstatusBits address satp value)
    (<["x10" := RVal_Bits value]> regs), global) prefix29 done /\
  prefix28 = writeSuccess15694Observation (writeSuccess15694Local
    (writeSuccess156d0Trace29 mstatusBits address satp value)
    (<["x10" := RVal_Bits value]> regs)) global :: prefix29.
Proof.
  intros Hdest Hprefix Hnil Hdone. have HdoneNb := seqStepSourceBlocking _ _ _ _ _ _ Hdone.
  destruct (writeSuccess15694TakeStep _ _ _ Hprefix ltac:(cbn; discriminate) Hnil HdoneNb)
    as (? & l29 & g29 & ? & p29 & Ho28 & Hs28 & ? & Hp29).
  eapply writeSuccessWriteRegCovered in Hs28.
  2: reflexivity. 2: exact Hdest. 2: reflexivity. 2: reflexivity.
  destruct Hs28 as (-> & -> & -> & ->). exists p29. split; first exact Hp29.
  rewrite Ho28. reflexivity.
Qed.
Print Assumptions segment_156d0_post_dest_covered.
