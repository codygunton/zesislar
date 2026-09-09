From Coq Require Import Eqdep_dec Lists.List.
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Contracts.InstructionBoundary.
Require Import ZesuSsz.Experiments.WriteSuccessCoverageAutomation.
Require Import ZesuSsz.Experiments.WriteSuccessSegment15694.
Require Import ZesuSsz.Experiments.WriteSuccessSegment101f0.

Definition writeSuccess101f0SuffixFirstObservations regs global
    (mstatusBits address satp value : bv 64) :=
  map (fun trace => writeSuccess15694Observation
    (writeSuccess15694Local trace regs) global)
    [writeSuccess101f0Trace22 mstatusBits address satp;
     writeSuccess101f0Trace23 mstatusBits address satp;
     writeSuccess101f0Trace24 mstatusBits address satp value;
     writeSuccess101f0Trace25 mstatusBits address satp value].

Lemma segment_101f0_suffix_first_covered regs global
    (mstatusBits address satp value : bv 64)
    prefix21 done labels spawned after :
  regs !! "satp" = Some (RVal_Bits satp) ->
  regs !! "x13" = Some (RVal_Bits value) ->
  IslaInstructionPrefixPath
    (writeSuccess15694Local
      (writeSuccess101f0Trace21 mstatusBits address) regs, global)
    prefix21 done ->
  done.1.(seq_trace) = tnil ->
  seq_step done.1 done.2 labels after.1 after.2 spawned ->
  exists prefix25,
    IslaInstructionPrefixPath
      (writeSuccess15694Local
        (writeSuccess101f0Trace25 mstatusBits address satp value) regs, global)
      prefix25 done /\
    prefix21 = writeSuccess101f0SuffixFirstObservations regs global
      mstatusBits address satp value ++ prefix25.
Proof.
  intros Hsatp Hx13 Hprefix Hnil Hdone.
  have HdoneNb := seqStepSourceBlocking _ _ _ _ _ _ Hdone.
  destruct (writeSuccess15694TakeStep _ _ _ Hprefix
    ltac:(cbn; discriminate) Hnil HdoneNb) as
    (? & l22 & g22 & ? & p22 & Ho21 & Hs21 & ? & Hp22).
  pose (b22 := (l22,g22)).
  eapply writeSuccessDeclareConstBitVecCovered in Hs21; [|reflexivity].
  destruct Hs21 as (declSatp & -> & -> & -> & ->).
  destruct (writeSuccess15694TakeStep _ _ _ Hp22
    ltac:(unfold b22; cbn; discriminate) Hnil HdoneNb) as
    (? & l23 & g23 & ? & p23 & Ho22 & Hs22 & Hnb23 & Hp23).
  pose (b23 := (l23,g23)). eapply writeSuccessReadRegCovered in Hs22.
  2: reflexivity. 2: exact Hsatp. 2: reflexivity. 2: exact Hnb23.
  destruct Hs22 as (-> & -> & -> & -> & HsymSatp).
  cbn in HsymSatp. injection HsymSatp as HsatpValue.
  pose proof (inj_pair2_eq_dec N N.eq_dec (fun width => bv width) 64%N
    declSatp satp HsatpValue) as HsatpBits. subst declSatp.
  destruct (writeSuccess15694TakeStep _ _ _ Hp23
    ltac:(unfold b23; cbn; discriminate) Hnil HdoneNb) as
    (? & l24 & g24 & ? & p24 & Ho23 & Hs23 & ? & Hp24).
  pose (b24 := (l24,g24)).
  eapply writeSuccessDeclareConstBitVecCovered in Hs23; [|reflexivity].
  destruct Hs23 as (declValue & -> & -> & -> & ->).
  destruct (writeSuccess15694TakeStep _ _ _ Hp24
    ltac:(unfold b24; cbn; discriminate) Hnil HdoneNb) as
    (? & l25 & g25 & ? & p25 & Ho24 & Hs24 & Hnb25 & Hp25).
  eapply writeSuccessReadRegCovered in Hs24.
  2: reflexivity. 2: exact Hx13. 2: reflexivity. 2: exact Hnb25.
  destruct Hs24 as (-> & -> & -> & -> & HsymValue).
  cbn in HsymValue. injection HsymValue as HvalueValue.
  pose proof (inj_pair2_eq_dec N N.eq_dec (fun width => bv width) 64%N
    declValue value HvalueValue) as HvalueBits. subst declValue.
  exists p25. split; first exact Hp25.
  unfold writeSuccess101f0SuffixFirstObservations. cbn.
  rewrite Ho21. rewrite Ho22. rewrite Ho23. rewrite Ho24. reflexivity.
Qed.

Print Assumptions segment_101f0_suffix_first_covered.
