Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Contracts.InstructionBoundary.
Require Import ZesuSsz.Experiments.WriteSuccessCoverageAutomation.
Require Import ZesuSsz.Experiments.WriteSuccessSegment15694.
Require Import ZesuSsz.Experiments.WriteSuccessSegment156d0.
Lemma segment_156d0_post_sign_covered regs global mstatusBits address satp value
    prefix27 done labels spawned after :
  IslaInstructionPrefixPath (writeSuccess15694Local
    (writeSuccess156d0Trace27 mstatusBits address satp value) regs, global)
    prefix27 done -> done.1.(seq_trace) = tnil ->
  seq_step done.1 done.2 labels after.1 after.2 spawned ->
  exists prefix28, IslaInstructionPrefixPath (writeSuccess15694Local
    (writeSuccess156d0Trace28 mstatusBits address satp value) regs, global)
    prefix28 done /\ prefix27 = writeSuccess15694Observation (writeSuccess15694Local
    (writeSuccess156d0Trace28 mstatusBits address satp value) regs) global :: prefix28.
Proof.
  intros Hprefix Hnil Hdone. have HdoneNb := seqStepSourceBlocking _ _ _ _ _ _ Hdone.
  destruct (writeSuccess15694TakeStep _ _ _ Hprefix ltac:(cbn; discriminate) Hnil HdoneNb)
    as (? & l28 & g28 & ? & p28 & Ho27 & Hs27 & ? & Hp28).
  eapply writeSuccessDefineConstCovered in Hs27.
  2: reflexivity. 2: { cbn. rewrite writeSuccess156d0SignExtendIdentity. reflexivity. }
  destruct Hs27 as (-> & -> & -> & ->). exists p28. split; first exact Hp28.
  rewrite Ho27. reflexivity.
Qed.
Print Assumptions segment_156d0_post_sign_covered.
