From Coq Require Import Eqdep_dec Lists.List.
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Contracts.InstructionBoundary.
Require Import ZesuSsz.Experiments.WriteSuccessCoverageAutomation.
Require Import ZesuSsz.Experiments.WriteSuccessSegment15694.
Require Import ZesuSsz.Experiments.WriteSuccessSegment156a8.

Definition writeSuccess156a8SuffixFirstObservations regs global
    (mstatusBits address satp value : bv 64) :=
  map (fun trace => writeSuccess15694Observation (writeSuccess15694Local trace regs) global)
    [writeSuccess156a8Trace22 mstatusBits address satp;
     writeSuccess156a8Trace23 mstatusBits address satp;
     writeSuccess156a8Trace24 mstatusBits address satp;
     writeSuccess156a8Trace25 mstatusBits address satp;
     writeSuccess156a8Trace26 mstatusBits address satp value].

Lemma segment_156a8_suffix_first_covered regs global
    (mstatusBits address satp : bv 64) prefix21 done labels spawned after :
  regs !! "satp" = Some (RVal_Bits satp) ->
  IslaInstructionPrefixPath (writeSuccess15694Local
    (writeSuccess156a8Trace21 mstatusBits address) regs, global) prefix21 done ->
  done.1.(seq_trace) = tnil -> seq_step done.1 done.2 labels after.1 after.2 spawned ->
  exists value prefix26,
    IslaInstructionPrefixPath (writeSuccess15694Local
      (writeSuccess156a8Trace26 mstatusBits address satp value) regs, global)
      prefix26 done /\
    prefix21 = writeSuccess156a8SuffixFirstObservations regs global
      mstatusBits address satp value ++ prefix26.
Proof.
  intros Hsatp Hprefix Hnil Hdone.
  have HdoneNb := seqStepSourceBlocking _ _ _ _ _ _ Hdone.
  destruct (writeSuccess15694TakeStep _ _ _ Hprefix ltac:(cbn; discriminate) Hnil HdoneNb)
    as (? & l22 & g22 & ? & p22 & Ho21 & Hs21 & ? & Hp22).
  pose (b22 := (l22,g22)). eapply writeSuccessDeclareConstBitVecCovered in Hs21; [|reflexivity].
  destruct Hs21 as (declSatp & -> & -> & -> & ->).
  destruct (writeSuccess15694TakeStep _ _ _ Hp22 ltac:(unfold b22; cbn; discriminate) Hnil HdoneNb)
    as (? & l23 & g23 & ? & p23 & Ho22 & Hs22 & Hnb23 & Hp23).
  pose (b23 := (l23,g23)). eapply writeSuccessReadRegCovered in Hs22.
  2: reflexivity. 2: exact Hsatp. 2: reflexivity. 2: exact Hnb23.
  destruct Hs22 as (-> & -> & -> & -> & HsymSatp). cbn in HsymSatp.
  injection HsymSatp as HsatpValue.
  pose proof (inj_pair2_eq_dec N N.eq_dec (fun width => bv width) 64%N
    declSatp satp HsatpValue) as HsatpBits. subst declSatp.
  destruct (writeSuccess15694TakeStep _ _ _ Hp23 ltac:(unfold b23; cbn; discriminate) Hnil HdoneNb)
    as (? & l24 & g24 & ? & p24 & Ho23 & Hs23 & ? & Hp24).
  pose (b24 := (l24,g24)). eapply writeSuccessDefineConstCovered in Hs23;
    [|reflexivity|reflexivity]. destruct Hs23 as (-> & -> & -> & ->).
  destruct (writeSuccess15694TakeStep _ _ _ Hp24 ltac:(unfold b24; cbn; discriminate) Hnil HdoneNb)
    as (? & l25 & g25 & ? & p25 & Ho24 & Hs24 & ? & Hp25).
  pose (b25 := (l25,g25)). eapply writeSuccessDefineConstCovered in Hs24;
    [|reflexivity|reflexivity]. destruct Hs24 as (-> & -> & -> & ->).
  destruct (writeSuccess15694TakeStep _ _ _ Hp25 ltac:(unfold b25; cbn; discriminate) Hnil HdoneNb)
    as (? & l26 & g26 & ? & p26 & Ho25 & Hs25 & ? & Hp26).
  eapply writeSuccessDeclareConstBitVecCovered in Hs25; [|reflexivity].
  destruct Hs25 as (value & -> & -> & -> & ->).
  exists value, p26. split; first exact Hp26.
  unfold writeSuccess156a8SuffixFirstObservations. cbn.
  rewrite Ho21. rewrite Ho22. rewrite Ho23. rewrite Ho24. rewrite Ho25. reflexivity.
Qed.
Print Assumptions segment_156a8_suffix_first_covered.
