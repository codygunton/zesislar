From Coq Require Import Eqdep_dec Lists.List.
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Contracts.InstructionBoundary.
Require Import ZesuSsz.Experiments.WriteSuccessCoverageAutomation.
Require Import ZesuSsz.Experiments.WriteSuccessSegment15694.
Require Import ZesuSsz.Experiments.WriteSuccessSegment101e4.

Definition writeSuccess101e4SuffixFirstObservations regs global
    (mstatusBits address satp : bv 64) :=
  map (fun trace => writeSuccess15694Observation
    (writeSuccess15694Local trace regs) global)
    [writeSuccess101e4Trace22 mstatusBits address satp;
     writeSuccess101e4Trace23 mstatusBits address satp;
     writeSuccess101e4Trace24 mstatusBits address satp;
     writeSuccess101e4Trace25 mstatusBits address satp].

Lemma segment_101e4_suffix_first_covered regs global
    (mstatusBits address satp : bv 64) prefix21 done labels spawned after :
  regs !! "satp" = Some (RVal_Bits satp) ->
  IslaInstructionPrefixPath
    (writeSuccess15694Local
      (writeSuccess101e4Trace21 mstatusBits address) regs, global)
    prefix21 done ->
  done.1.(seq_trace) = tnil ->
  seq_step done.1 done.2 labels after.1 after.2 spawned ->
  exists prefix25,
    IslaInstructionPrefixPath
      (writeSuccess15694Local
        (writeSuccess101e4Trace25 mstatusBits address satp) regs, global)
      prefix25 done /\
    prefix21 = writeSuccess101e4SuffixFirstObservations regs global
      mstatusBits address satp ++ prefix25.
Proof.
  intros Hsatp Hprefix Hnil Hdone.
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
  pose (b24 := (l24,g24)). eapply writeSuccessDefineConstCovered in Hs23;
    [|reflexivity|reflexivity]. destruct Hs23 as (-> & -> & -> & ->).
  destruct (writeSuccess15694TakeStep _ _ _ Hp24
    ltac:(unfold b24; cbn; discriminate) Hnil HdoneNb) as
    (? & l25 & g25 & ? & p25 & Ho24 & Hs24 & ? & Hp25).
  eapply writeSuccessDefineConstCovered in Hs24;
    [|reflexivity|reflexivity]. destruct Hs24 as (-> & -> & -> & ->).
  exists p25. split; first exact Hp25.
  unfold writeSuccess101e4SuffixFirstObservations. cbn.
  rewrite Ho21. rewrite Ho22. rewrite Ho23. rewrite Ho24. reflexivity.
Qed.

Print Assumptions segment_101e4_suffix_first_covered.
