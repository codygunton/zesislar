Require Import isla.riscv64.riscv64.
Require Import IslaTraces.write_success_91.a156a8.
Require Import IslaTraces.write_success_91.a156ac.
Require Import ZesuSsz.Contracts.InstructionBoundary.
Require Import ZesuSsz.Experiments.WriteSuccessSegment15694.
Require Import ZesuSsz.Experiments.WriteSuccessSegment156a8.
Require Import ZesuSsz.Experiments.WriteSuccessSegment156a8CoveragePrefix.
Require Import ZesuSsz.Experiments.WriteSuccessSegment156a8CoverageSecond.
Require Import ZesuSsz.Experiments.WriteSuccessSegment156a8CoverageMiddleFirst.
Require Import ZesuSsz.Experiments.WriteSuccessSegment156a8CoverageMiddleSecond.
Require Import ZesuSsz.Experiments.WriteSuccessSegment156a8CoverageSuffix.

Lemma segment_156a8_covered (regs : reg_map) (global : seq_global_state)
    (mstatusBits address satp value oldDest : bv 64) observations after :
  regs !! "PC" = Some (RVal_Bits (Z_to_bv 64 0x156a8)) ->
  regs !! "x2" = Some (RVal_Bits address) ->
  regs !! "mstatus" = Some (RegVal_Struct [("bits", RVal_Bits mstatusBits)]) ->
  regs !! "satp" = Some (RVal_Bits satp) ->
  regs !! "x10" = Some (RVal_Bits oldDest) ->
  writeSuccess156a8SysRegs regs ->
  eval_a_exp regs writeSuccess15694Mstatus = Some (Val_Bool true) ->
  eval_a_exp regs writeSuccess156a8Aligned = Some (Val_Bool true) ->
  eval_a_exp regs writeSuccess156a8Lower = Some (Val_Bool true) ->
  eval_a_exp regs writeSuccess156a8Upper = Some (Val_Bool true) ->
  read_mem global.(seq_mem) (bv_unsigned (writeSuccess156a8Address address)) 8 =
    Some (bv_to_bvn value) ->
  global.(seq_instrs) !! Z_to_bv 64 0x156a8 = Some a156a8 ->
  global.(seq_instrs) !! Z_to_bv 64 0x156ac = Some a156ac ->
  IslaInstructionSegment (writeSuccess156a8Before regs global) observations after ->
  after = writeSuccess156a8After regs global value /\
  observations = writeSuccess156a8Observations regs global
    mstatusBits address satp value.
Proof.
  intros Hpc Hx2 Hmstatus Hsatp Hdest Hsys HmstatusAssume Haligned Hlower Hupper
    Hmem Hcode Hnext Hsegment.
  destruct (segment_156a8_prefix5_covered regs global mstatusBits address satp value
    observations after Hsys Hsegment) as
    (done & labels & spawned & prefix5 & Hp5 & Hnil & Hdone & Hend & Hobs).
  destruct (segment_156a8_second5_covered regs global mstatusBits address satp value
    prefix5 done labels spawned after Hsys Hp5 Hnil Hdone) as (prefix10 & Hp10 & Hobs2).
  destruct (segment_156a8_middle_first_covered regs global prefix10 done labels spawned
    after HmstatusAssume Haligned Hlower Hupper Hp10 Hnil Hdone) as
    (declMstatus & declAddress & prefix15 & Hp15 & Hobs3).
  destruct (segment_156a8_middle_second_covered regs global declMstatus declAddress
    mstatusBits address prefix15 done labels spawned after Hpc Hx2 Hmstatus Hupper
    Hp15 Hnil Hdone) as (-> & -> & prefix21 & Hp21 & Hobs4).
  destruct (segment_156a8_suffix_backed_covered regs global mstatusBits address satp
    value oldDest prefix21 done labels spawned after Hpc Hsatp Hdest Hmem Hnext Hp21 Hnil Hdone)
    as (Hafter & Hobs5). subst after.
  split; first reflexivity. rewrite Hobs. rewrite Hobs2. rewrite Hobs3. rewrite Hobs4.
  repeat rewrite <- app_assoc. cbn [List.app]. rewrite Hobs5.
  unfold writeSuccess156a8Observations,
    writeSuccess156a8ExecutionPrefix,
    writeSuccess156a8PreReadObservations,
    writeSuccess156a8PostReadPrefix,
    writeSuccess156a8First5Observations,
    writeSuccess156a8Second5Observations,
    writeSuccess156a8MiddleFirstObservations,
    writeSuccess156a8MiddleSecondObservations,
    writeSuccess156a8SuffixObservations,
    writeSuccess156a8PrefixObservations. cbn. reflexivity.
Qed.

Lemma segment_156a8_mmio_covered (regs : reg_map) (global : seq_global_state)
    (mstatusBits address satp oldDest : bv 64) observations after :
  regs !! "PC" = Some (RVal_Bits (Z_to_bv 64 0x156a8)) ->
  regs !! "x2" = Some (RVal_Bits address) ->
  regs !! "mstatus" = Some (RegVal_Struct [("bits", RVal_Bits mstatusBits)]) ->
  regs !! "satp" = Some (RVal_Bits satp) ->
  regs !! "x10" = Some (RVal_Bits oldDest) ->
  writeSuccess156a8SysRegs regs ->
  eval_a_exp regs writeSuccess15694Mstatus = Some (Val_Bool true) ->
  eval_a_exp regs writeSuccess156a8Aligned = Some (Val_Bool true) ->
  eval_a_exp regs writeSuccess156a8Lower = Some (Val_Bool true) ->
  eval_a_exp regs writeSuccess156a8Upper = Some (Val_Bool true) ->
  read_mem global.(seq_mem) (bv_unsigned (writeSuccess156a8Address address)) 8 = None ->
  global.(seq_instrs) !! Z_to_bv 64 0x156a8 = Some a156a8 ->
  global.(seq_instrs) !! Z_to_bv 64 0x156ac = Some a156ac ->
  IslaInstructionSegment (writeSuccess156a8Before regs global) observations after ->
  exists value,
  after = writeSuccess156a8After regs global value /\
  observations = writeSuccess156a8MmioObservations regs global
    mstatusBits address satp value.
Proof.
  intros Hpc Hx2 Hmstatus Hsatp Hdest Hsys HmstatusAssume Haligned Hlower Hupper
    Hmem Hcode Hnext Hsegment.
  destruct (segment_156a8_prefix5_covered regs global mstatusBits address satp oldDest
    observations after Hsys Hsegment) as
    (done & labels & spawned & prefix5 & Hp5 & Hnil & Hdone & Hend & Hobs).
  destruct (segment_156a8_second5_covered regs global mstatusBits address satp oldDest
    prefix5 done labels spawned after Hsys Hp5 Hnil Hdone) as (prefix10 & Hp10 & Hobs2).
  destruct (segment_156a8_middle_first_covered regs global prefix10 done labels spawned
    after HmstatusAssume Haligned Hlower Hupper Hp10 Hnil Hdone) as
    (declMstatus & declAddress & prefix15 & Hp15 & Hobs3).
  destruct (segment_156a8_middle_second_covered regs global declMstatus declAddress
    mstatusBits address prefix15 done labels spawned after Hpc Hx2 Hmstatus Hupper
    Hp15 Hnil Hdone) as (-> & -> & prefix21 & Hp21 & Hobs4).
  destruct (segment_156a8_suffix_mmio_covered regs global mstatusBits address satp
    oldDest prefix21 done labels spawned after Hpc Hsatp Hdest Hmem Hnext Hp21 Hnil Hdone)
    as (value & Hafter & Hobs5).
  subst after. exists value. split; first reflexivity.
  rewrite Hobs. rewrite Hobs2. rewrite Hobs3. rewrite Hobs4.
  repeat rewrite <- app_assoc. cbn [List.app]. rewrite Hobs5.
  unfold writeSuccess156a8MmioObservations,
    writeSuccess156a8ExecutionPrefix,
    writeSuccess156a8PreReadObservations,
    writeSuccess156a8PostReadPrefix,
    writeSuccess156a8First5Observations,
    writeSuccess156a8Second5Observations,
    writeSuccess156a8MiddleFirstObservations,
    writeSuccess156a8MiddleSecondObservations,
    writeSuccess156a8SuffixObservations,
    writeSuccess156a8PrefixObservations. cbn. reflexivity.
Qed.

Print Assumptions segment_156a8_covered.
Print Assumptions segment_156a8_mmio_covered.
