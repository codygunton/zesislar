Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Contracts.InstructionBoundary.
Require Import ZesuSsz.Experiments.WriteSuccessSegmentAutomation.
Require Import ZesuSsz.Experiments.WriteSuccessCoverageAutomation.
Require Import ZesuSsz.Experiments.WriteSuccessSegment15694.
Require Import ZesuSsz.Experiments.WriteSuccessSegment15d28.

Lemma segment_15d28_suffix_first1_covered regs global prefix8 done :
  IslaInstructionPrefixPath
    (writeSuccess15694Local writeSuccess15d28Trace8 regs, global) prefix8 done ->
  done.1.(seq_trace) = tnil -> done.1.(seq_nb_state) = false ->
  exists prefix9,
    IslaInstructionPrefixPath
      (writeSuccess15694Local writeSuccess15d28Trace9 regs, global) prefix9 done /\
    prefix8 = [writeSuccess15694Observation
      (writeSuccess15694Local writeSuccess15d28Trace9 regs) global] ++ prefix9.
Proof.
  intros Hprefix Hnil Hnb.
  destruct (writeSuccess15694TakeStep _ _ _ Hprefix
    ltac:(cbn; discriminate) Hnil Hnb) as
    (? & local & nextGlobal & ? & rest & Hobs & Hstep & ? & Hrest).
  eapply writeSuccessDefineConstCovered in Hstep; [|reflexivity|reflexivity].
  destruct Hstep as (-> & -> & -> & ->).
  exists rest. split; first exact Hrest. cbn. rewrite Hobs. reflexivity.
Qed.
Print Assumptions segment_15d28_suffix_first1_covered.
