Require Import isla.riscv64.riscv64.
Require Import IslaTraces.write_success_02.a101e4.
Require Import IslaTraces.write_success_02.a101e8.
Require Import ZesuSsz.Contracts.InstructionBoundary.
Require Import ZesuSsz.Experiments.WriteSuccessSegment15694.
Require Import ZesuSsz.Experiments.WriteSuccessSegment101e4.
Require Import ZesuSsz.Experiments.WriteSuccessSegment101e4CoveragePrefix.
Require Import ZesuSsz.Experiments.WriteSuccessSegment101e4CoverageSecond.
Require Import ZesuSsz.Experiments.WriteSuccessSegment101e4CoverageMiddleFirst.
Require Import ZesuSsz.Experiments.WriteSuccessSegment101e4CoverageMiddleSecond.
Require Import ZesuSsz.Experiments.WriteSuccessSegment101e4CoverageSuffixFirst.
Require Import ZesuSsz.Experiments.WriteSuccessSegment101e4CoverageSuffix.

Lemma segment_101e4_covered (regs : reg_map) (global : seq_global_state)
    (mstatusBits address satp : bv 64) (byte : bv 8)
    observations after :
  regs !! "PC" = Some (RVal_Bits (Z_to_bv 64 0x101e4)) ->
  regs !! "x13" = Some (RVal_Bits address) ->
  regs !! "mstatus" = Some
    (RegVal_Struct [("bits", RVal_Bits mstatusBits)]) ->
  regs !! "satp" = Some (RVal_Bits satp) ->
  writeSuccess101e4SysRegs regs ->
  read_mem global.(seq_mem) (bv_unsigned address) 1 = Some (bv_to_bvn byte) ->
  global.(seq_instrs) !! Z_to_bv 64 0x101e4 = Some a101e4 ->
  global.(seq_instrs) !! Z_to_bv 64 0x101e8 = Some a101e8 ->
  eval_a_exp regs writeSuccess15694Mstatus = Some (Val_Bool true) ->
  eval_a_exp regs writeSuccess101e4Lower = Some (Val_Bool true) ->
  eval_a_exp regs writeSuccess101e4Upper = Some (Val_Bool true) ->
  IslaInstructionSegment (writeSuccess101e4Before regs global)
    observations after ->
  after = writeSuccess101e4After regs global byte /\
  observations =
    writeSuccess101e4Observations regs global mstatusBits address satp byte.
Proof.
  intros Hpc Hx13 Hmstatus Hsatp Hsys Hmem Hcode Hnext
    HmstatusAssume Hlower Hupper Hsegment.
  destruct (segment_101e4_prefix5_covered regs global mstatusBits address satp byte
    observations after Hsys Hsegment) as
    (done & labels & spawned & prefix5 & Hp5 & Hnil & Hdone & Hend & Hobs).
  destruct (segment_101e4_second5_covered regs global mstatusBits address satp byte
    prefix5 done labels spawned after Hsys Hp5 Hnil Hdone) as
    (prefix10 & Hp10 & HobsSecond).
  destruct (segment_101e4_middle_first_covered regs global prefix10 done
    labels spawned after HmstatusAssume Hlower Hupper Hp10 Hnil Hdone) as
    (declMstatus & declAddress & prefix15 & Hp15 & HobsMiddleFirst).
  destruct (segment_101e4_middle_second_covered regs global declMstatus
    declAddress mstatusBits address prefix15 done labels spawned after
    Hpc Hx13 Hmstatus Hp15 Hnil Hdone) as
    (HdeclMstatus & HdeclAddress & prefix21 & Hp21 & HobsMiddleSecond).
  subst declMstatus declAddress.
  destruct (segment_101e4_suffix_first_covered regs global mstatusBits address
    satp prefix21 done labels spawned after Hsatp Hp21 Hnil Hdone) as
    (prefix25 & Hp25 & HobsSuffixFirst).
  destruct (segment_101e4_suffix_covered regs global mstatusBits address satp byte
    prefix25 done labels spawned after Hpc Hx13 Hmem Hnext Hp25 Hnil Hdone) as
    (Hafter & HobsSuffix).
  subst after. split; first reflexivity.
  rewrite Hobs. rewrite HobsSecond. rewrite HobsMiddleFirst.
  rewrite HobsMiddleSecond. rewrite HobsSuffixFirst.
  repeat rewrite <- app_assoc. rewrite HobsSuffix.
  unfold writeSuccess101e4Observations,
    writeSuccess101e4PrefixObservations,
    writeSuccess101e4First5Observations,
    writeSuccess101e4Second5Observations,
    writeSuccess101e4MiddleFirstObservations,
    writeSuccess101e4MiddleSecondObservations,
    writeSuccess101e4SuffixFirstObservations,
    writeSuccess101e4SuffixObservations. cbn. reflexivity.
Qed.

Print Assumptions segment_101e4_covered.
