Require Import isla.riscv64.riscv64.
Require Import IslaTraces.write_success_02.a101f0.
Require Import IslaTraces.write_success_02.a101f4.
Require Import ZesuSsz.Contracts.InstructionBoundary.
Require Import ZesuSsz.Experiments.WriteSuccessSegment15694.
Require Import ZesuSsz.Experiments.WriteSuccessSegment101f0.
Require Import ZesuSsz.Experiments.WriteSuccessSegment101f0CoveragePrefix.
Require Import ZesuSsz.Experiments.WriteSuccessSegment101f0CoverageSecond.
Require Import ZesuSsz.Experiments.WriteSuccessSegment101f0CoverageMiddleFirst.
Require Import ZesuSsz.Experiments.WriteSuccessSegment101f0CoverageMiddleSecond.
Require Import ZesuSsz.Experiments.WriteSuccessSegment101f0CoverageSuffixFirst.
Require Import ZesuSsz.Experiments.WriteSuccessSegment101f0CoverageSuffix.

Lemma segment_101f0_covered (regs : reg_map) (global : seq_global_state)
    (mstatusBits address satp value : bv 64) old observations after :
  regs !! "PC" = Some (RVal_Bits (Z_to_bv 64 0x101f0)) ->
  regs !! "x14" = Some (RVal_Bits address) ->
  regs !! "mstatus" = Some
    (RegVal_Struct [("bits", RVal_Bits mstatusBits)]) ->
  regs !! "satp" = Some (RVal_Bits satp) ->
  regs !! "x13" = Some (RVal_Bits value) ->
  writeSuccess101f0SysRegs regs ->
  eval_a_exp regs writeSuccess15694Mstatus = Some (Val_Bool true) ->
  eval_a_exp regs writeSuccess101f0Lower = Some (Val_Bool true) ->
  eval_a_exp regs writeSuccess101f0Upper = Some (Val_Bool true) ->
  read_mem global.(seq_mem) (bv_unsigned address) 1 = Some old ->
  global.(seq_instrs) !! Z_to_bv 64 0x101f0 = Some a101f0 ->
  global.(seq_instrs) !! Z_to_bv 64 0x101f4 = Some a101f4 ->
  IslaInstructionSegment (writeSuccess101f0Before regs global)
    observations after ->
  exists result,
  after = writeSuccess101f0After regs global address value /\
  observations = writeSuccess101f0Observations regs global
    mstatusBits address satp value result.
Proof.
  intros Hpc Hx14 Hmstatus Hsatp Hx13 Hsys HmstatusAssume Hlower Hupper
    Hmem Hcode Hnext Hsegment.
  destruct (segment_101f0_prefix5_covered regs global mstatusBits address satp value
    observations after Hsys Hsegment) as
    (done & labels & spawned & prefix5 & Hp5 & Hnil & Hdone & Hend & Hobs).
  destruct (segment_101f0_second5_covered regs global mstatusBits address satp value
    prefix5 done labels spawned after Hsys Hp5 Hnil Hdone) as
    (prefix10 & Hp10 & HobsSecond).
  destruct (segment_101f0_middle_first_covered regs global prefix10 done
    labels spawned after HmstatusAssume Hlower Hupper Hp10 Hnil Hdone) as
    (declMstatus & declAddress & prefix15 & Hp15 & HobsMiddleFirst).
  destruct (segment_101f0_middle_second_covered regs global declMstatus
    declAddress mstatusBits address prefix15 done labels spawned after
    Hpc Hx14 Hmstatus Hp15 Hnil Hdone) as
    (HdeclMstatus & HdeclAddress & prefix21 & Hp21 & HobsMiddleSecond).
  subst declMstatus declAddress.
  destruct (segment_101f0_suffix_first_covered regs global mstatusBits address
    satp value prefix21 done labels spawned after Hsatp Hx13 Hp21 Hnil Hdone) as
    (prefix25 & Hp25 & HobsSuffixFirst).
  destruct (segment_101f0_suffix_covered regs global mstatusBits address satp value
    old prefix25 done labels spawned after Hpc Hmem Hnext Hp25 Hnil Hdone) as
    (result & Hafter & HobsSuffix).
  subst after. exists result. split; first reflexivity.
  rewrite Hobs. rewrite HobsSecond. rewrite HobsMiddleFirst.
  rewrite HobsMiddleSecond. rewrite HobsSuffixFirst.
  repeat rewrite <- app_assoc. rewrite HobsSuffix.
  unfold writeSuccess101f0Observations,
    writeSuccess101f0PrefixObservations,
    writeSuccess101f0First5Observations,
    writeSuccess101f0Second5Observations,
    writeSuccess101f0MiddleFirstObservations,
    writeSuccess101f0MiddleSecondObservations,
    writeSuccess101f0SuffixFirstObservations,
    writeSuccess101f0SuffixObservations. cbn. reflexivity.
Qed.

Print Assumptions segment_101f0_covered.
