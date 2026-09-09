Require Import isla.riscv64.riscv64.
Require Import IslaTraces.write_success_07.a15d14.
Require Import IslaTraces.write_success_07.a15d18.
Require Import ZesuSsz.Contracts.InstructionBoundary.
Require Import ZesuSsz.Experiments.WriteSuccessSegment15694.
Require Import ZesuSsz.Experiments.WriteSuccessSegment15d14.
Require Import ZesuSsz.Experiments.WriteSuccessSegment15d14CoveragePrefix.
Require Import ZesuSsz.Experiments.WriteSuccessSegment15d14CoverageSecond.
Require Import ZesuSsz.Experiments.WriteSuccessSegment15d14CoverageMiddleFirst.
Require Import ZesuSsz.Experiments.WriteSuccessSegment15d14CoverageMiddleSecond.
Require Import ZesuSsz.Experiments.WriteSuccessSegment15d14CoverageSuffixFirst.
Require Import ZesuSsz.Experiments.WriteSuccessSegment15d14CoverageSuffix.

Lemma segment_15d14_covered (regs : reg_map) (global : seq_global_state)
    (mstatusBits address satp value : bv 64) old observations after :
  regs !! "PC" = Some (RVal_Bits (Z_to_bv 64 0x15d14)) ->
  regs !! "x2" = Some (RVal_Bits address) ->
  regs !! "mstatus" = Some
    (RegVal_Struct [("bits", RVal_Bits mstatusBits)]) ->
  regs !! "satp" = Some (RVal_Bits satp) ->
  regs !! "x1" = Some (RVal_Bits value) ->
  writeSuccess15d14SysRegs regs ->
  eval_a_exp regs writeSuccess15694Mstatus = Some (Val_Bool true) ->
  eval_a_exp regs writeSuccess15d14Aligned = Some (Val_Bool true) ->
  eval_a_exp regs writeSuccess15d14Lower = Some (Val_Bool true) ->
  eval_a_exp regs writeSuccess15d14Upper = Some (Val_Bool true) ->
  read_mem global.(seq_mem)
    (bv_unsigned (writeSuccess15d14Address address)) 8 = Some old ->
  global.(seq_instrs) !! Z_to_bv 64 0x15d14 = Some a15d14 ->
  global.(seq_instrs) !! Z_to_bv 64 0x15d18 = Some a15d18 ->
  IslaInstructionSegment (writeSuccess15d14Before regs global)
    observations after ->
  exists result,
  after = writeSuccess15d14After regs global address value /\
  observations = writeSuccess15d14Observations regs global
    mstatusBits address satp value result.
Proof.
  intros Hpc Hx2 Hmstatus Hsatp Hx1 Hsys HmstatusAssume Haligned Hlower Hupper
    Hmem Hcode Hnext Hsegment.
  destruct (segment_15d14_prefix5_covered regs global mstatusBits address satp value
    observations after Hsys Hsegment) as
    (done & labels & spawned & prefix5 & Hp5 & Hnil & Hdone & Hend & Hobs).
  destruct (segment_15d14_second5_covered regs global mstatusBits address satp value
    prefix5 done labels spawned after Hsys Hp5 Hnil Hdone) as
    (prefix10 & Hp10 & HobsSecond).
  destruct (segment_15d14_middle_first_covered regs global prefix10 done
    labels spawned after HmstatusAssume Haligned Hlower Hupper Hp10 Hnil Hdone) as
    (declMstatus & declAddress & prefix15 & Hp15 & HobsMiddleFirst).
  destruct (segment_15d14_middle_second_covered regs global declMstatus
    declAddress mstatusBits address prefix15 done labels spawned after
    Hpc Hx2 Hmstatus Hupper Hp15 Hnil Hdone) as
    (HdeclMstatus & HdeclAddress & prefix21 & Hp21 & HobsMiddleSecond).
  subst declMstatus declAddress.
  destruct (segment_15d14_suffix_first_covered regs global mstatusBits address
    satp value prefix21 done labels spawned after Hsatp Hx1 Hp21 Hnil Hdone) as
    (prefix25 & Hp25 & HobsSuffixFirst).
  destruct (segment_15d14_suffix_covered regs global mstatusBits address satp value
    old prefix25 done labels spawned after Hpc Hmem Hnext Hp25 Hnil Hdone) as
    (result & Hafter & HobsSuffix).
  subst after. exists result. split; first reflexivity.
  rewrite Hobs. rewrite HobsSecond. rewrite HobsMiddleFirst.
  rewrite HobsMiddleSecond. rewrite HobsSuffixFirst.
  repeat rewrite <- app_assoc. rewrite HobsSuffix.
  unfold writeSuccess15d14Observations,
    writeSuccess15d14PrefixObservations,
    writeSuccess15d14First5Observations,
    writeSuccess15d14Second5Observations,
    writeSuccess15d14MiddleFirstObservations,
    writeSuccess15d14MiddleSecondObservations,
    writeSuccess15d14SuffixFirstObservations,
    writeSuccess15d14SuffixObservations. cbn. reflexivity.
Qed.

Lemma segment_15d14_mmio_covered (regs : reg_map) (global : seq_global_state)
    (mstatusBits address satp value : bv 64) observations after :
  regs !! "PC" = Some (RVal_Bits (Z_to_bv 64 0x15d14)) ->
  regs !! "x2" = Some (RVal_Bits address) ->
  regs !! "mstatus" = Some
    (RegVal_Struct [("bits", RVal_Bits mstatusBits)]) ->
  regs !! "satp" = Some (RVal_Bits satp) ->
  regs !! "x1" = Some (RVal_Bits value) ->
  writeSuccess15d14SysRegs regs ->
  eval_a_exp regs writeSuccess15694Mstatus = Some (Val_Bool true) ->
  eval_a_exp regs writeSuccess15d14Aligned = Some (Val_Bool true) ->
  eval_a_exp regs writeSuccess15d14Lower = Some (Val_Bool true) ->
  eval_a_exp regs writeSuccess15d14Upper = Some (Val_Bool true) ->
  read_mem global.(seq_mem)
    (bv_unsigned (writeSuccess15d14Address address)) 8 = None ->
  (bv_unsigned (writeSuccess15d14Address address) + 8 <= 2 ^ 64)%Z ->
  set_Forall (fun item =>
    ~ (bv_unsigned (writeSuccess15d14Address address) <= bv_unsigned item <
       bv_unsigned (writeSuccess15d14Address address) + 8)%Z)
    (dom global.(seq_mem)) ->
  global.(seq_instrs) !! Z_to_bv 64 0x15d14 = Some a15d14 ->
  global.(seq_instrs) !! Z_to_bv 64 0x15d18 = Some a15d18 ->
  IslaInstructionSegment (writeSuccess15d14Before regs global)
    observations after ->
  exists result,
  after = writeSuccess15d14MmioAfter regs global /\
  observations = writeSuccess15d14MmioObservations regs global
    mstatusBits address satp value result.
Proof.
  intros Hpc Hx2 Hmstatus Hsatp Hx1 Hsys HmstatusAssume Haligned Hlower Hupper
    Hmem Hrange Houtside Hcode Hnext Hsegment.
  destruct (segment_15d14_prefix5_covered regs global mstatusBits address satp value
    observations after Hsys Hsegment) as
    (done & labels & spawned & prefix5 & Hp5 & Hnil & Hdone & Hend & Hobs).
  destruct (segment_15d14_second5_covered regs global mstatusBits address satp value
    prefix5 done labels spawned after Hsys Hp5 Hnil Hdone) as
    (prefix10 & Hp10 & HobsSecond).
  destruct (segment_15d14_middle_first_covered regs global prefix10 done
    labels spawned after HmstatusAssume Haligned Hlower Hupper Hp10 Hnil Hdone) as
    (declMstatus & declAddress & prefix15 & Hp15 & HobsMiddleFirst).
  destruct (segment_15d14_middle_second_covered regs global declMstatus
    declAddress mstatusBits address prefix15 done labels spawned after
    Hpc Hx2 Hmstatus Hupper Hp15 Hnil Hdone) as
    (HdeclMstatus & HdeclAddress & prefix21 & Hp21 & HobsMiddleSecond).
  subst declMstatus declAddress.
  destruct (segment_15d14_suffix_first_covered regs global mstatusBits address
    satp value prefix21 done labels spawned after Hsatp Hx1 Hp21 Hnil Hdone) as
    (prefix25 & Hp25 & HobsSuffixFirst).
  destruct (segment_15d14_mmio_suffix_covered regs global mstatusBits address satp value
    prefix25 done labels spawned after Hpc Hmem Hnext Hp25 Hnil Hdone) as
    (result & Hafter & HobsSuffix).
  subst after. exists result. split; first reflexivity.
  rewrite Hobs. rewrite HobsSecond. rewrite HobsMiddleFirst.
  rewrite HobsMiddleSecond. rewrite HobsSuffixFirst.
  repeat rewrite <- app_assoc. rewrite HobsSuffix.
  unfold writeSuccess15d14MmioObservations,
    writeSuccess15d14MmioPrefixObservations,
    writeSuccess15d14First5Observations,
    writeSuccess15d14Second5Observations,
    writeSuccess15d14MiddleFirstObservations,
    writeSuccess15d14MiddleSecondObservations,
    writeSuccess15d14SuffixFirstObservations,
    writeSuccess15d14MmioSuffixObservations. cbn. reflexivity.
Qed.

Print Assumptions segment_15d14_covered.
Print Assumptions segment_15d14_mmio_covered.
