Require Import isla.riscv64.riscv64.
Require Import IslaTraces.write_success_07.a15d2c.
Require Import IslaTraces.write_success_07.a15d30.
Require Import ZesuSsz.Contracts.InstructionBoundary.
Require Import ZesuSsz.Experiments.WriteSuccessSegment15694.
Require Import ZesuSsz.Experiments.WriteSuccessSegment15d2c.
Require Import ZesuSsz.Experiments.WriteSuccessSegment15d2cCoveragePrefix.
Require Import ZesuSsz.Experiments.WriteSuccessSegment15d2cCoverageSecond.
Require Import ZesuSsz.Experiments.WriteSuccessSegment15d2cCoverageMiddleFirst.
Require Import ZesuSsz.Experiments.WriteSuccessSegment15d2cCoverageMiddleSecond.
Require Import ZesuSsz.Experiments.WriteSuccessSegment15d2cCoverageSuffix.

Lemma segment_15d2c_covered (regs : reg_map) (global : seq_global_state)
    (mstatusBits address satp value oldDest : bv 64) observations after :
  regs !! "PC" = Some (RVal_Bits (Z_to_bv 64 0x15d2c)) ->
  regs !! "x2" = Some (RVal_Bits address) ->
  regs !! "mstatus" = Some (RegVal_Struct [("bits", RVal_Bits mstatusBits)]) ->
  regs !! "satp" = Some (RVal_Bits satp) ->
  regs !! "x1" = Some (RVal_Bits oldDest) ->
  writeSuccess15d2cSysRegs regs ->
  eval_a_exp regs writeSuccess15694Mstatus = Some (Val_Bool true) ->
  eval_a_exp regs writeSuccess15d2cAligned = Some (Val_Bool true) ->
  eval_a_exp regs writeSuccess15d2cLower = Some (Val_Bool true) ->
  eval_a_exp regs writeSuccess15d2cUpper = Some (Val_Bool true) ->
  read_mem global.(seq_mem) (bv_unsigned (writeSuccess15d2cAddress address)) 8 =
    Some (bv_to_bvn value) ->
  global.(seq_instrs) !! Z_to_bv 64 0x15d2c = Some a15d2c ->
  global.(seq_instrs) !! Z_to_bv 64 0x15d30 = Some a15d30 ->
  IslaInstructionSegment (writeSuccess15d2cBefore regs global) observations after ->
  after = writeSuccess15d2cAfter regs global value /\
  observations = writeSuccess15d2cObservations regs global
    mstatusBits address satp value.
Proof.
  intros Hpc Hx2 Hmstatus Hsatp Hdest Hsys HmstatusAssume Haligned Hlower Hupper
    Hmem Hcode Hnext Hsegment.
  destruct (segment_15d2c_prefix5_covered regs global mstatusBits address satp value
    observations after Hsys Hsegment) as
    (done & labels & spawned & prefix5 & Hp5 & Hnil & Hdone & Hend & Hobs).
  destruct (segment_15d2c_second5_covered regs global mstatusBits address satp value
    prefix5 done labels spawned after Hsys Hp5 Hnil Hdone) as (prefix10 & Hp10 & Hobs2).
  destruct (segment_15d2c_middle_first_covered regs global prefix10 done labels spawned
    after HmstatusAssume Haligned Hlower Hupper Hp10 Hnil Hdone) as
    (declMstatus & declAddress & prefix15 & Hp15 & Hobs3).
  destruct (segment_15d2c_middle_second_covered regs global declMstatus declAddress
    mstatusBits address prefix15 done labels spawned after Hpc Hx2 Hmstatus Hupper
    Hp15 Hnil Hdone) as (-> & -> & prefix21 & Hp21 & Hobs4).
  destruct (segment_15d2c_suffix_backed_covered regs global mstatusBits address satp
    value oldDest prefix21 done labels spawned after Hpc Hsatp Hdest Hmem Hnext Hp21 Hnil Hdone)
    as (Hafter & Hobs5). subst after.
  split; first reflexivity. rewrite Hobs. rewrite Hobs2. rewrite Hobs3. rewrite Hobs4.
  repeat rewrite <- app_assoc. cbn [List.app]. rewrite Hobs5.
  unfold writeSuccess15d2cObservations,
    writeSuccess15d2cExecutionPrefix,
    writeSuccess15d2cPreReadObservations,
    writeSuccess15d2cPostReadPrefix,
    writeSuccess15d2cFirst5Observations,
    writeSuccess15d2cSecond5Observations,
    writeSuccess15d2cMiddleFirstObservations,
    writeSuccess15d2cMiddleSecondObservations,
    writeSuccess15d2cSuffixObservations,
    writeSuccess15d2cPrefixObservations. cbn. reflexivity.
Qed.

Lemma segment_15d2c_mmio_covered (regs : reg_map) (global : seq_global_state)
    (mstatusBits address satp oldDest : bv 64) observations after :
  regs !! "PC" = Some (RVal_Bits (Z_to_bv 64 0x15d2c)) ->
  regs !! "x2" = Some (RVal_Bits address) ->
  regs !! "mstatus" = Some (RegVal_Struct [("bits", RVal_Bits mstatusBits)]) ->
  regs !! "satp" = Some (RVal_Bits satp) ->
  regs !! "x1" = Some (RVal_Bits oldDest) ->
  writeSuccess15d2cSysRegs regs ->
  eval_a_exp regs writeSuccess15694Mstatus = Some (Val_Bool true) ->
  eval_a_exp regs writeSuccess15d2cAligned = Some (Val_Bool true) ->
  eval_a_exp regs writeSuccess15d2cLower = Some (Val_Bool true) ->
  eval_a_exp regs writeSuccess15d2cUpper = Some (Val_Bool true) ->
  read_mem global.(seq_mem) (bv_unsigned (writeSuccess15d2cAddress address)) 8 = None ->
  global.(seq_instrs) !! Z_to_bv 64 0x15d2c = Some a15d2c ->
  global.(seq_instrs) !! Z_to_bv 64 0x15d30 = Some a15d30 ->
  IslaInstructionSegment (writeSuccess15d2cBefore regs global) observations after ->
  exists value,
  after = writeSuccess15d2cAfter regs global value /\
  observations = writeSuccess15d2cMmioObservations regs global
    mstatusBits address satp value.
Proof.
  intros Hpc Hx2 Hmstatus Hsatp Hdest Hsys HmstatusAssume Haligned Hlower Hupper
    Hmem Hcode Hnext Hsegment.
  destruct (segment_15d2c_prefix5_covered regs global mstatusBits address satp oldDest
    observations after Hsys Hsegment) as
    (done & labels & spawned & prefix5 & Hp5 & Hnil & Hdone & Hend & Hobs).
  destruct (segment_15d2c_second5_covered regs global mstatusBits address satp oldDest
    prefix5 done labels spawned after Hsys Hp5 Hnil Hdone) as (prefix10 & Hp10 & Hobs2).
  destruct (segment_15d2c_middle_first_covered regs global prefix10 done labels spawned
    after HmstatusAssume Haligned Hlower Hupper Hp10 Hnil Hdone) as
    (declMstatus & declAddress & prefix15 & Hp15 & Hobs3).
  destruct (segment_15d2c_middle_second_covered regs global declMstatus declAddress
    mstatusBits address prefix15 done labels spawned after Hpc Hx2 Hmstatus Hupper
    Hp15 Hnil Hdone) as (-> & -> & prefix21 & Hp21 & Hobs4).
  destruct (segment_15d2c_suffix_mmio_covered regs global mstatusBits address satp
    oldDest prefix21 done labels spawned after Hpc Hsatp Hdest Hmem Hnext Hp21 Hnil Hdone)
    as (value & Hafter & Hobs5).
  subst after. exists value. split; first reflexivity.
  rewrite Hobs. rewrite Hobs2. rewrite Hobs3. rewrite Hobs4.
  repeat rewrite <- app_assoc. cbn [List.app]. rewrite Hobs5.
  unfold writeSuccess15d2cMmioObservations,
    writeSuccess15d2cExecutionPrefix,
    writeSuccess15d2cPreReadObservations,
    writeSuccess15d2cPostReadPrefix,
    writeSuccess15d2cFirst5Observations,
    writeSuccess15d2cSecond5Observations,
    writeSuccess15d2cMiddleFirstObservations,
    writeSuccess15d2cMiddleSecondObservations,
    writeSuccess15d2cSuffixObservations,
    writeSuccess15d2cPrefixObservations. cbn. reflexivity.
Qed.

Print Assumptions segment_15d2c_covered.
Print Assumptions segment_15d2c_mmio_covered.
