Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Contracts.InstructionBoundary.
Require Import ZesuSsz.Experiments.WriteSuccessSegment15694.
Require Import ZesuSsz.Experiments.WriteSuccessSegment156d8.
Require Import ZesuSsz.Experiments.WriteSuccessSegment156d8CoverageSuffixFirstOne.
Require Import ZesuSsz.Experiments.WriteSuccessSegment156d8CoverageSuffixSecondOne.

Lemma segment_156d8_suffix_first2_covered regs global prefix8 done :
  IslaInstructionPrefixPath
    (writeSuccess15694Local writeSuccess156d8Trace8 regs, global)
    prefix8 done ->
  done.1.(seq_trace) = tnil ->
  done.1.(seq_nb_state) = false ->
  exists prefix10,
    IslaInstructionPrefixPath
      (writeSuccess15694Local writeSuccess156d8Trace10 regs, global)
      prefix10 done /\
    prefix8 = writeSuccess156d8TailFirst2Observations regs global ++ prefix10.
Proof.
  intros Hprefix Hnil Hnb.
  destruct (segment_156d8_suffix_first1_covered regs global prefix8 done
    Hprefix Hnil Hnb) as (prefix9 & Hprefix9 & Hobs8).
  destruct (segment_156d8_suffix_second1_covered regs global prefix9 done
    Hprefix9 Hnil Hnb) as (prefix10 & Hprefix10 & Hobs9).
  exists prefix10. split; first exact Hprefix10.
  rewrite Hobs8 Hobs9. unfold writeSuccess156d8TailFirst2Observations.
  cbn. reflexivity.
Qed.
Print Assumptions segment_156d8_suffix_first2_covered.
