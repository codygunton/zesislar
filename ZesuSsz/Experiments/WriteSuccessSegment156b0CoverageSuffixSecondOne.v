Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Contracts.InstructionBoundary.
Require Import ZesuSsz.Experiments.WriteSuccessSegmentAutomation.
Require Import ZesuSsz.Experiments.WriteSuccessCoverageAutomation.
Require Import ZesuSsz.Experiments.WriteSuccessSegment15694.
Require Import ZesuSsz.Experiments.WriteSuccessSegment156b0.

Lemma segment_156b0_suffix_second1_covered regs global prefix9 done :
  IslaInstructionPrefixPath
    (writeSuccess15694Local writeSuccess156b0Trace9 regs, global) prefix9 done ->
  done.1.(seq_trace) = tnil -> done.1.(seq_nb_state) = false ->
  exists prefix10,
    IslaInstructionPrefixPath
      (writeSuccess15694Local writeSuccess156b0Trace10 regs, global) prefix10 done /\
    prefix9 = [writeSuccess15694Observation
      (writeSuccess15694Local writeSuccess156b0Trace10 regs) global] ++ prefix10.
Proof.
  intros Hprefix Hnil Hnb.
  destruct (writeSuccess15694TakeStep _ _ _ Hprefix
    ltac:(cbn; discriminate) Hnil Hnb) as
    (? & local & nextGlobal & ? & rest & Hobs & Hstep & ? & Hrest).
  eapply writeSuccessDefineConstCovered in Hstep; [|reflexivity|reflexivity].
  destruct Hstep as (-> & -> & -> & ->).
  exists rest. split; first exact Hrest. cbn. rewrite Hobs. reflexivity.
Qed.
Print Assumptions segment_156b0_suffix_second1_covered.
