From Coq Require Import Eqdep_dec Lists.List.
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Contracts.InstructionBoundary.
Require Import ZesuSsz.Experiments.WriteSuccessCoverageAutomation.
Require Import ZesuSsz.Experiments.WriteSuccessSegment15694.
Require Import ZesuSsz.Experiments.WriteSuccessSegment15d18.

Definition writeSuccess15d18MiddleSecondObservations regs global
    mstatusBits address :=
  map (fun trace => writeSuccess15694Observation
    (writeSuccess15694Local trace regs) global)
    [writeSuccess15d18TraceUpper mstatusBits address;
     writeSuccess15d18Trace16 mstatusBits address;
     writeSuccess15d18Trace17 mstatusBits address;
     writeSuccess15d18Trace18 mstatusBits address;
     writeSuccess15d18Trace19 mstatusBits address;
     writeSuccess15d18Trace20 mstatusBits address;
     writeSuccess15d18Trace21 mstatusBits address].

Lemma segment_15d18_middle_second_covered regs global
    (declMstatus declAddress actualMstatus actualAddress : bv 64)
    prefix15 done labels spawned after :
  regs !! "PC" = Some (RVal_Bits (Z_to_bv 64 0x15d18)) ->
  regs !! "x2" = Some (RVal_Bits actualAddress) ->
  regs !! "mstatus" = Some
    (RegVal_Struct [("bits", RVal_Bits actualMstatus)]) ->
  eval_a_exp regs writeSuccess15d18Upper = Some (Val_Bool true) ->
  IslaInstructionPrefixPath
    (writeSuccess15694Local
      (writeSuccess15d18Trace15 declMstatus declAddress) regs, global)
    prefix15 done ->
  done.1.(seq_trace) = tnil ->
  seq_step done.1 done.2 labels after.1 after.2 spawned ->
  declMstatus = actualMstatus /\
  declAddress = actualAddress /\
  exists prefix21,
    IslaInstructionPrefixPath
      (writeSuccess15694Local
        (writeSuccess15d18Trace21 actualMstatus actualAddress) regs, global)
      prefix21 done /\
    prefix15 = writeSuccess15d18MiddleSecondObservations regs global
      actualMstatus actualAddress ++ prefix21.
Proof.
  intros Hpc Hx10 Hmstatus Hupper Hprefix Hnil Hdone.
  have HdoneNb := seqStepSourceBlocking _ _ _ _ _ _ Hdone.
  destruct (writeSuccess15694TakeStep _ _ _ Hprefix
    ltac:(cbn; discriminate) Hnil HdoneNb) as
    (? & lu & gu & ? & pu & Hou & Hsu & ? & Hpu).
  pose (bu := (lu,gu)). eapply writeSuccessAssumeCovered in Hsu;
    [|reflexivity|exact Hupper]. destruct Hsu as (-> & -> & -> & ->).
  destruct (writeSuccess15694TakeStep _ _ _ Hpu
    ltac:(unfold bu; cbn; discriminate) Hnil HdoneNb) as
    (? & l16 & g16 & ? & p16 & Ho15 & Hs15 & ? & Hp16).
  pose (b16 := (l16,g16)).
  eapply writeSuccessDeclareConstBitVecCovered in Hs15; [|reflexivity].
  destruct Hs15 as (pcBits & -> & -> & -> & ->).
  destruct (writeSuccess15694TakeStep _ _ _ Hp16
    ltac:(unfold b16; cbn; discriminate) Hnil HdoneNb) as
    (? & l17 & g17 & ? & p17 & Ho16 & Hs16 & Hnb17 & Hp17).
  pose (b17 := (l17,g17)). eapply writeSuccessReadRegCovered in Hs16.
  2: reflexivity. 2: exact Hpc. 2: reflexivity. 2: exact Hnb17.
  destruct Hs16 as (-> & -> & -> & -> & HsymPc).
  cbn in HsymPc. injection HsymPc as HpcValue.
  pose proof (inj_pair2_eq_dec N N.eq_dec (fun width => bv width) 64%N
    pcBits (Z_to_bv 64 0x15d18) HpcValue) as HpcBits.
  subst pcBits.
  destruct (writeSuccess15694TakeStep _ _ _ Hp17
    ltac:(unfold b17; cbn; discriminate) Hnil HdoneNb) as
    (? & l18 & g18 & ? & p18 & Ho17 & Hs17 & ? & Hp18).
  pose (b18 := (l18,g18)).
  eapply writeSuccessDefineConstCovered in Hs17; [|reflexivity|reflexivity].
  destruct Hs17 as (-> & -> & -> & ->).
  destruct (writeSuccess15694TakeStep _ _ _ Hp18
    ltac:(unfold b18; cbn; discriminate) Hnil HdoneNb) as
    (? & l19 & g19 & ? & p19 & Ho18 & Hs18 & Hnb19 & Hp19).
  pose (b19 := (l19,g19)). eapply writeSuccessReadRegCovered in Hs18.
  2: reflexivity. 2: exact Hx10. 2: reflexivity. 2: exact Hnb19.
  destruct Hs18 as (-> & -> & -> & -> & HsymAddress).
  cbn in HsymAddress. injection HsymAddress as HaddressValue.
  pose proof (inj_pair2_eq_dec N N.eq_dec (fun width => bv width) 64%N
    declAddress actualAddress HaddressValue) as HaddressBits.
  subst declAddress.
  destruct (writeSuccess15694TakeStep _ _ _ Hp19
    ltac:(unfold b19; cbn; discriminate) Hnil HdoneNb) as
    (? & l20 & g20 & ? & p20 & Ho19 & Hs19 & ? & Hp20).
  pose (b20 := (l20,g20)).
  eapply writeSuccessDefineConstCovered in Hs19.
  2: reflexivity.
  2: { cbn. destruct (decide (64%N = 64%N)) as [Heq|Hneq].
       - rewrite (UIP_dec N.eq_dec Heq eq_refl). cbn.
         reflexivity.
       - exfalso. apply Hneq. reflexivity. }
  destruct Hs19 as (-> & -> & -> & ->).
  destruct (writeSuccess15694TakeStep _ _ _ Hp20
    ltac:(unfold b20; cbn; discriminate) Hnil HdoneNb) as
    (? & l21 & g21 & ? & p21 & Ho20 & Hs20 & Hnb21 & Hp21).
  eapply writeSuccessReadRegCovered in Hs20.
  2: reflexivity. 2: exact Hmstatus. 2: reflexivity. 2: exact Hnb21.
  destruct Hs20 as (-> & -> & -> & -> & HsymMstatus).
  cbn in HsymMstatus. injection HsymMstatus as HmstatusValue.
  injection HmstatusValue as HmstatusBitsValue.
  pose proof (inj_pair2_eq_dec N N.eq_dec (fun width => bv width) 64%N
    declMstatus actualMstatus HmstatusBitsValue) as HmstatusBits.
  subst declMstatus.
  repeat split; try reflexivity. exists p21. split; first exact Hp21.
  unfold writeSuccess15d18MiddleSecondObservations. cbn.
  rewrite Hou.
  rewrite Ho15. rewrite Ho16. rewrite Ho17. rewrite Ho18. rewrite Ho19.
  rewrite Ho20. reflexivity.
Qed.

Print Assumptions segment_15d18_middle_second_covered.
