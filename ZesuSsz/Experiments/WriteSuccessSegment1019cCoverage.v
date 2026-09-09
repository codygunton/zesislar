Require Import isla.riscv64.riscv64.
Require Import IslaTraces.write_success_01.a1019c.
Require Import IslaTraces.write_success_01.a101a0.
Require Import ZesuSsz.Contracts.InstructionBoundary.
Require Import ZesuSsz.Experiments.WriteSuccessSegment15694.
Require Import ZesuSsz.Experiments.WriteSuccessSegment1019c.
Require Import ZesuSsz.Experiments.WriteSuccessStoreOutcome.
Require Import ZesuSsz.Experiments.WriteSuccessSegment1019cCoveragePrefix.
Require Import ZesuSsz.Experiments.WriteSuccessSegment1019cCoverageSecond.
Require Import ZesuSsz.Experiments.WriteSuccessSegment1019cCoverageMiddleFirst.
Require Import ZesuSsz.Experiments.WriteSuccessSegment1019cCoverageMiddleSecond.
Require Import ZesuSsz.Experiments.WriteSuccessSegment1019cCoverageSuffixFirst.
Require Import ZesuSsz.Experiments.WriteSuccessSegment1019cCoverageSuffixMiddle.
Require Import ZesuSsz.Experiments.WriteSuccessSegment1019cCoverageSuffix.

Lemma segment_1019c_covered (regs : reg_map) (global : seq_global_state)
    (mstatusBits base satp value : bv 64) observations after :
  regs !! "PC" = Some (RVal_Bits (Z_to_bv 64 0x1019c)) ->
  regs !! "x5" = Some (RVal_Bits base) ->
  regs !! "mstatus" = Some
    (RegVal_Struct [("bits", RVal_Bits mstatusBits)]) ->
  regs !! "satp" = Some (RVal_Bits satp) ->
  regs !! "x11" = Some (RVal_Bits value) ->
  writeSuccess1019cSysRegs regs ->
  eval_a_exp regs writeSuccess15694Mstatus = Some (Val_Bool true) ->
  eval_a_exp regs writeSuccess1019cAlign = Some (Val_Bool true) ->
  eval_a_exp regs writeSuccess1019cLower = Some (Val_Bool true) ->
  eval_a_exp regs writeSuccess1019cUpper = Some (Val_Bool true) ->
  global.(seq_instrs) !! Z_to_bv 64 0x1019c = Some a1019c ->
  global.(seq_instrs) !! Z_to_bv 64 0x101a0 = Some a101a0 ->
  IslaInstructionSegment (writeSuccess1019cBefore regs global)
    observations after ->
  exists result outcome,
    writeSuccessStoreOutcomePermitted global
      (writeSuccess1019cAddress base) outcome /\
    after = writeSuccess1019cAfter regs global base value outcome /\
    observations = writeSuccess1019cObservations regs global
      mstatusBits base satp value result outcome.
Proof.
  intros Hpc Hx5 Hmstatus Hsatp Hvalue Hsys HmstatusAssume Halign Hlower
    Hupper Hcode Hnext Hsegment.
  destruct (segment_1019c_prefix5_covered regs global mstatusBits base satp value
    observations after Hsys Hsegment) as
    (done & labels & spawned & prefix5 & Hp5 & Hnil & Hdone & Hend & Hobs).
  destruct (segment_1019c_second5_covered regs global mstatusBits base satp value
    prefix5 done labels spawned after Hsys Hp5 Hnil Hdone) as
    (prefix10 & Hp10 & HobsSecond).
  destruct (segment_1019c_middle_first_covered regs global prefix10 done
    labels spawned after HmstatusAssume Halign Hlower Hupper Hp10 Hnil Hdone) as
    (declMstatus & declBase & prefix16 & Hp16 & HobsMiddleFirst).
  destruct (segment_1019c_middle_second_covered regs global declMstatus
    declBase mstatusBits base prefix16 done labels spawned after
    Hpc Hx5 Hmstatus Hp16 Hnil Hdone) as
    (HdeclMstatus & HdeclBase & prefix22 & Hp22 & HobsMiddleSecond).
  subst declMstatus declBase.
  destruct (segment_1019c_suffix_first_covered regs global mstatusBits base
    satp value prefix22 done labels spawned after Hsatp Hvalue Hp22 Hnil Hdone) as
    (prefix26 & Hp26 & HobsSuffixFirst).
  destruct (segment_1019c_suffix_middle_covered regs global mstatusBits base
    satp value prefix26 done labels spawned after Hp26 Hnil Hdone) as
    (result & prefix29 & Hp29 & HobsSuffixMiddle).
  destruct (segment_1019c_suffix_covered regs global mstatusBits base satp value
    result prefix29 done labels spawned after Hpc Hnext Hp29 Hnil Hdone) as
    (outcome & Hpermitted & Hafter & HobsSuffix).
  subst after. exists result, outcome. split; first exact Hpermitted.
  split; first reflexivity.
  rewrite Hobs. rewrite HobsSecond. rewrite HobsMiddleFirst.
  rewrite HobsMiddleSecond. rewrite HobsSuffixFirst.
  rewrite HobsSuffixMiddle.
  repeat rewrite <- app_assoc. rewrite HobsSuffix.
  unfold writeSuccess1019cObservations,
    writeSuccess1019cPrefixObservations,
    writeSuccess1019cFirst5Observations,
    writeSuccess1019cSecond5Observations,
    writeSuccess1019cMiddleFirstObservations,
    writeSuccess1019cMiddleSecondObservations,
    writeSuccess1019cSuffixFirstObservations,
    writeSuccess1019cSuffixMiddleObservations,
    writeSuccess1019cSuffixObservations. cbn. reflexivity.
Qed.

Print Assumptions segment_1019c_covered.
