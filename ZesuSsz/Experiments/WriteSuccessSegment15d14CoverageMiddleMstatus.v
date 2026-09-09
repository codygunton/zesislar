From Coq Require Import Eqdep_dec Lists.List.
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Contracts.InstructionBoundary.
Require Import ZesuSsz.Experiments.WriteSuccessCoverageAutomation.
Require Import ZesuSsz.Experiments.WriteSuccessSegment15694.
Require Import ZesuSsz.Experiments.WriteSuccessSegment15d14.

Lemma segment_15d14_middle_mstatus_covered regs global
    (declMstatus actualMstatus address : bv 64) prefix done labels spawned after :
  regs !! "mstatus" = Some (RegVal_Struct [("bits", RVal_Bits actualMstatus)]) ->
  IslaInstructionPrefixPath
    (writeSuccess15694Local (writeSuccess15d14Trace20 declMstatus address) regs, global) prefix done ->
  done.1.(seq_trace) = tnil -> seq_step done.1 done.2 labels after.1 after.2 spawned ->
  declMstatus = actualMstatus /\ exists rest, IslaInstructionPrefixPath
    (writeSuccess15694Local (writeSuccess15d14Trace21 actualMstatus address) regs, global) rest done /\
  prefix = [writeSuccess15694Observation
    (writeSuccess15694Local (writeSuccess15d14Trace21 actualMstatus address) regs) global] ++ rest.
Proof.
  intros Hmstatus Hprefix Hnil Hdone. have HdoneNb := seqStepSourceBlocking _ _ _ _ _ _ Hdone.
  destruct (writeSuccess15694TakeStep _ _ _ Hprefix ltac:(cbn; discriminate) Hnil HdoneNb) as
    (? & l21 & g21 & ? & p21 & Ho20 & Hs20 & Hnb21 & Hp21).
  eapply writeSuccessReadRegCovered in Hs20.
  2: reflexivity. 2: exact Hmstatus. 2: reflexivity. 2: exact Hnb21.
  destruct Hs20 as (-> & -> & -> & -> & HsymMstatus). cbn in HsymMstatus.
  injection HsymMstatus as HmstatusValue. injection HmstatusValue as HmstatusBitsValue.
  pose proof (inj_pair2_eq_dec N N.eq_dec (fun width => bv width) 64%N
    declMstatus actualMstatus HmstatusBitsValue) as HmstatusBits. subst declMstatus.
  split; first reflexivity. exists p21. split; first exact Hp21. cbn. rewrite Ho20. reflexivity.
Qed.
Print Assumptions segment_15d14_middle_mstatus_covered.
