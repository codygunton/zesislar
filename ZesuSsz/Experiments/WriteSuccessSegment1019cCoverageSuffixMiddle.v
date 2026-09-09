From Coq Require Import Lists.List.
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Contracts.InstructionBoundary.
Require Import ZesuSsz.Experiments.WriteSuccessCoverageAutomation.
Require Import ZesuSsz.Experiments.WriteSuccessSegment15694.
Require Import ZesuSsz.Experiments.WriteSuccessSegment1019c.
Require Import ZesuSsz.Experiments.WriteSuccessStoreOutcome.

Definition writeSuccess1019cSuffixMiddleObservations regs global
    (mstatusBits base satp value : bv 64) (result : bool) :=
  [writeSuccess15694Observation
     (writeSuccess15694Local
       (writeSuccess1019cTrace27 mstatusBits base satp value) regs) global;
   writeSuccess15694Observation
     (writeSuccess15694Local
       (writeSuccess1019cTrace28 mstatusBits base satp value) regs) global;
   writeSuccess15694Observation
     (writeSuccess15694Local
       (writeSuccess1019cTrace29 mstatusBits base satp value result) regs) global].

Lemma segment_1019c_suffix_middle_covered regs global
    (mstatusBits base satp value : bv 64)
    prefix26 done labels spawned after :
  IslaInstructionPrefixPath
    (writeSuccess15694Local
      (writeSuccess1019cTrace26 mstatusBits base satp value) regs, global)
    prefix26 done ->
  done.1.(seq_trace) = tnil ->
  seq_step done.1 done.2 labels after.1 after.2 spawned ->
  exists result prefix29,
    IslaInstructionPrefixPath
      (writeSuccess15694Local
        (writeSuccess1019cTrace29 mstatusBits base satp value result) regs,
       global) prefix29 done /\
    prefix26 = writeSuccess1019cSuffixMiddleObservations regs global
      mstatusBits base satp value result ++ prefix29.
Proof.
  intros Hprefix Hnil Hdone.
  have HdoneNb := seqStepSourceBlocking _ _ _ _ _ _ Hdone.
  destruct (writeSuccess15694TakeStep _ _ _ Hprefix
    ltac:(cbn; discriminate) Hnil HdoneNb) as
    (? & l27 & g27 & ? & p27 & Ho26 & Hs26 & ? & Hp27).
  pose (b27 := (l27,g27)).
  eapply writeSuccessDefineConstCovered in Hs26;
    [|reflexivity|reflexivity]. destruct Hs26 as (-> & -> & -> & ->).
  destruct (writeSuccess15694TakeStep _ _ _ Hp27
    ltac:(unfold b27; cbn; discriminate) Hnil HdoneNb) as
    (? & l28 & g28 & ? & p28 & Ho27 & Hs27 & ? & Hp28).
  pose (b28 := (l28,g28)).
  eapply writeSuccessDefineConstCovered in Hs27;
    [|reflexivity|reflexivity]. destruct Hs27 as (-> & -> & -> & ->).
  destruct (writeSuccess15694TakeStep _ _ _ Hp28
    ltac:(unfold b28; cbn; discriminate) Hnil HdoneNb) as
    (? & l29 & g29 & ? & p29 & Ho28 & Hs28 & ? & Hp29).
  eapply writeSuccessDeclareConstBoolCovered in Hs28; [|reflexivity].
  destruct Hs28 as (result & -> & -> & -> & ->).
  exists result, p29. split; first exact Hp29.
  unfold writeSuccess1019cSuffixMiddleObservations. cbn.
  rewrite Ho26. rewrite Ho27. rewrite Ho28. reflexivity.
Qed.

Print Assumptions segment_1019c_suffix_middle_covered.
