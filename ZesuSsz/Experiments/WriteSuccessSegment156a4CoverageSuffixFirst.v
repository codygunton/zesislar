Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Contracts.InstructionBoundary.
Require Import ZesuSsz.Experiments.WriteSuccessSegmentAutomation.
Require Import ZesuSsz.Experiments.WriteSuccessCoverageAutomation.
Require Import ZesuSsz.Experiments.WriteSuccessSegment15694.
Require Import ZesuSsz.Experiments.WriteSuccessSegment156a4.

Lemma segment_156a4_suffix_first2_covered regs global prefix8 done :
  IslaInstructionPrefixPath
    (writeSuccess15694Local writeSuccess156a4Trace8 regs, global)
    prefix8 done ->
  done.1.(seq_trace) = tnil ->
  done.1.(seq_nb_state) = false ->
  exists prefix10,
    IslaInstructionPrefixPath
      (writeSuccess15694Local writeSuccess156a4Trace10 regs, global)
      prefix10 done /\
    prefix8 = writeSuccess156a4TailFirst2Observations regs global ++ prefix10.
Proof.
  intros Hprefix8 Hnil HdoneNb.
  destruct (writeSuccess15694TakeStep _ _ _ Hprefix8
    ltac:(cbn; discriminate) Hnil HdoneNb) as
    (? & local9 & global9 & ? & prefix9 & Hobs8 & Hstep8 & ? & Hprefix9).
  eapply writeSuccessDefineConstCovered in Hstep8; [|reflexivity|reflexivity].
  destruct Hstep8 as (-> & -> & -> & ->).
  destruct (writeSuccess15694TakeStep _ _ _ Hprefix9
    ltac:(cbn; discriminate) Hnil HdoneNb) as
    (? & local10 & global10 & ? & prefix10 & Hobs9 & Hstep9 & ? & Hprefix10).
  eapply writeSuccessDefineConstCovered in Hstep9; [|reflexivity|reflexivity].
  destruct Hstep9 as (-> & -> & -> & ->).
  exists prefix10. split; first exact Hprefix10.
  unfold writeSuccess156a4TailFirst2Observations. cbn.
  rewrite Hobs8. rewrite Hobs9. reflexivity.
Qed.

Print Assumptions segment_156a4_suffix_first2_covered.
