From Coq Require Import Eqdep_dec Lists.List.
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Contracts.InstructionBoundary.
Require Import ZesuSsz.Experiments.WriteSuccessCoverageAutomation.
Require Import ZesuSsz.Experiments.WriteSuccessSegment15694.
Require Import ZesuSsz.Experiments.WriteSuccessSegment10198.
Require Import ZesuSsz.Experiments.WriteSuccessSegment10198CoverageMiddleSecondPc.

Definition writeSuccess10198MiddleSecondObservations regs global
    mstatusBits base :=
  map (fun trace => writeSuccess15694Observation
    (writeSuccess15694Local trace regs) global)
    [writeSuccess10198Trace17 mstatusBits base;
     writeSuccess10198Trace18 mstatusBits base;
     writeSuccess10198Trace19 mstatusBits base;
     writeSuccess10198Trace20 mstatusBits base;
     writeSuccess10198Trace21 mstatusBits base;
     writeSuccess10198Trace22 mstatusBits base].

Lemma segment_10198_middle_second_covered regs global
    (declMstatus declBase actualMstatus actualBase : bv 64)
    prefix16 done labels spawned after :
  regs !! "PC" = Some (RVal_Bits (Z_to_bv 64 0x10198)) ->
  regs !! "x5" = Some (RVal_Bits actualBase) ->
  regs !! "mstatus" = Some
    (RegVal_Struct [("bits", RVal_Bits actualMstatus)]) ->
  IslaInstructionPrefixPath
    (writeSuccess15694Local
      (writeSuccess10198Trace16 declMstatus declBase) regs, global)
    prefix16 done ->
  done.1.(seq_trace) = tnil ->
  seq_step done.1 done.2 labels after.1 after.2 spawned ->
  declMstatus = actualMstatus /\
  declBase = actualBase /\
  exists prefix22,
    IslaInstructionPrefixPath
      (writeSuccess15694Local
        (writeSuccess10198Trace22 actualMstatus actualBase) regs, global)
      prefix22 done /\
    prefix16 = writeSuccess10198MiddleSecondObservations regs global
      actualMstatus actualBase ++ prefix22.
Proof.
  intros Hpc Hx5 Hmstatus Hprefix Hnil Hdone.
  destruct (segment_10198_middle_second_pc_covered regs global
    declMstatus declBase prefix16 done labels spawned after
    Hpc Hprefix Hnil Hdone) as (prefix19 & Hp19 & Hobs19).
  have HdoneNb := seqStepSourceBlocking _ _ _ _ _ _ Hdone.
  destruct (writeSuccess15694TakeStep _ _ _ Hp19
    ltac:(cbn; discriminate) Hnil HdoneNb) as
    (? & l20 & g20 & ? & p20 & Ho19 & Hs19 & Hnb20 & Hp20).
  pose (b20 := (l20,g20)). eapply writeSuccessReadRegCovered in Hs19.
  2: reflexivity. 2: exact Hx5. 2: reflexivity. 2: exact Hnb20.
  destruct Hs19 as (-> & -> & -> & -> & HsymBase).
  cbn in HsymBase. injection HsymBase as HbaseValue.
  pose proof (inj_pair2_eq_dec N N.eq_dec (fun width => bv width) 64%N
    declBase actualBase HbaseValue) as HbaseBits. subst declBase.
  destruct (writeSuccess15694TakeStep _ _ _ Hp20
    ltac:(unfold b20; cbn; discriminate) Hnil HdoneNb) as
    (? & l21 & g21 & ? & p21 & Ho20 & Hs20 & ? & Hp21).
  pose (b21 := (l21,g21)).
  eapply writeSuccessDefineConstCovered in Hs20.
  2: reflexivity.
  2: { cbn. destruct (decide (64%N = 64%N)) as [Heq|Hneq].
       - rewrite (UIP_dec N.eq_dec Heq eq_refl). cbn. reflexivity.
       - exfalso. apply Hneq. reflexivity. }
  destruct Hs20 as (-> & -> & -> & ->).
  destruct (writeSuccess15694TakeStep _ _ _ Hp21
    ltac:(unfold b21; cbn; discriminate) Hnil HdoneNb) as
    (? & l22 & g22 & ? & p22 & Ho21 & Hs21 & Hnb22 & Hp22).
  eapply writeSuccessReadRegCovered in Hs21.
  2: reflexivity. 2: exact Hmstatus. 2: reflexivity. 2: exact Hnb22.
  destruct Hs21 as (-> & -> & -> & -> & HsymMstatus).
  cbn in HsymMstatus. injection HsymMstatus as HmstatusValue.
  injection HmstatusValue as HmstatusBitsValue.
  pose proof (inj_pair2_eq_dec N N.eq_dec (fun width => bv width) 64%N
    declMstatus actualMstatus HmstatusBitsValue) as HmstatusBits.
  subst declMstatus.
  repeat split; try reflexivity. exists p22. split; first exact Hp22.
  rewrite Hobs19. unfold writeSuccess10198MiddleSecondObservations,
    writeSuccess10198MiddleSecondPcObservations. cbn.
  rewrite Ho19. rewrite Ho20. rewrite Ho21. reflexivity.
Qed.

Print Assumptions segment_10198_middle_second_covered.
