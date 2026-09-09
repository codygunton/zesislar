Require Import isla.riscv64.riscv64.
Require Import IslaTraces.write_success_01.a10198.
Require Import IslaTraces.write_success_01.a1019c.
Require Import ZesuSsz.Contracts.InstructionBoundary.
Require Import ZesuSsz.Experiments.WriteSuccessSegment15694.
Require Import ZesuSsz.Experiments.WriteSuccessSegment10198.
Require Import ZesuSsz.Experiments.WriteSuccessStoreOutcome.
Require Import ZesuSsz.Experiments.WriteSuccessSegment10198CoveragePrefix.
Require Import ZesuSsz.Experiments.WriteSuccessSegment10198CoverageSecond.
Require Import ZesuSsz.Experiments.WriteSuccessSegment10198CoverageMiddleFirst.
Require Import ZesuSsz.Experiments.WriteSuccessSegment10198CoverageMiddleSecond.
Require Import ZesuSsz.Experiments.WriteSuccessSegment10198CoverageSuffixFirst.
Require Import ZesuSsz.Experiments.WriteSuccessSegment10198CoverageSuffixMiddle.
Require Import ZesuSsz.Experiments.WriteSuccessSegment10198CoverageSuffix.

Lemma segment_10198_covered (regs : reg_map) (global : seq_global_state)
    (mstatusBits base satp value : bv 64) observations after :
  regs !! "PC" = Some (RVal_Bits (Z_to_bv 64 0x10198)) ->
  regs !! "x5" = Some (RVal_Bits base) ->
  regs !! "mstatus" = Some
    (RegVal_Struct [("bits", RVal_Bits mstatusBits)]) ->
  regs !! "satp" = Some (RVal_Bits satp) ->
  regs !! "x10" = Some (RVal_Bits value) ->
  writeSuccess10198SysRegs regs ->
  eval_a_exp regs writeSuccess15694Mstatus = Some (Val_Bool true) ->
  eval_a_exp regs writeSuccess10198Align = Some (Val_Bool true) ->
  eval_a_exp regs writeSuccess10198Lower = Some (Val_Bool true) ->
  eval_a_exp regs writeSuccess10198Upper = Some (Val_Bool true) ->
  global.(seq_instrs) !! Z_to_bv 64 0x10198 = Some a10198 ->
  global.(seq_instrs) !! Z_to_bv 64 0x1019c = Some a1019c ->
  IslaInstructionSegment (writeSuccess10198Before regs global)
    observations after ->
  exists result outcome,
    writeSuccessStoreOutcomePermitted global
      (writeSuccess10198Address base) outcome /\
    after = writeSuccess10198After regs global base value outcome /\
    observations = writeSuccess10198Observations regs global
      mstatusBits base satp value result outcome.
Proof.
  intros Hpc Hx5 Hmstatus Hsatp Hvalue Hsys HmstatusAssume Halign Hlower
    Hupper Hcode Hnext Hsegment.
  destruct (segment_10198_prefix5_covered regs global mstatusBits base satp value
    observations after Hsys Hsegment) as
    (done & labels & spawned & prefix5 & Hp5 & Hnil & Hdone & Hend & Hobs).
  destruct (segment_10198_second5_covered regs global mstatusBits base satp value
    prefix5 done labels spawned after Hsys Hp5 Hnil Hdone) as
    (prefix10 & Hp10 & HobsSecond).
  destruct (segment_10198_middle_first_covered regs global prefix10 done
    labels spawned after HmstatusAssume Halign Hlower Hupper Hp10 Hnil Hdone) as
    (declMstatus & declBase & prefix16 & Hp16 & HobsMiddleFirst).
  destruct (segment_10198_middle_second_covered regs global declMstatus
    declBase mstatusBits base prefix16 done labels spawned after
    Hpc Hx5 Hmstatus Hp16 Hnil Hdone) as
    (HdeclMstatus & HdeclBase & prefix22 & Hp22 & HobsMiddleSecond).
  subst declMstatus declBase.
  destruct (segment_10198_suffix_first_covered regs global mstatusBits base
    satp value prefix22 done labels spawned after Hsatp Hvalue Hp22 Hnil Hdone) as
    (prefix26 & Hp26 & HobsSuffixFirst).
  destruct (segment_10198_suffix_middle_covered regs global mstatusBits base
    satp value prefix26 done labels spawned after Hp26 Hnil Hdone) as
    (result & prefix29 & Hp29 & HobsSuffixMiddle).
  destruct (segment_10198_suffix_covered regs global mstatusBits base satp value
    result prefix29 done labels spawned after Hpc Hnext Hp29 Hnil Hdone) as
    (outcome & Hpermitted & Hafter & HobsSuffix).
  subst after. exists result, outcome. split; first exact Hpermitted.
  split; first reflexivity.
  rewrite Hobs. rewrite HobsSecond. rewrite HobsMiddleFirst.
  rewrite HobsMiddleSecond. rewrite HobsSuffixFirst.
  rewrite HobsSuffixMiddle.
  repeat rewrite <- app_assoc. rewrite HobsSuffix.
  unfold writeSuccess10198Observations,
    writeSuccess10198PrefixObservations,
    writeSuccess10198First5Observations,
    writeSuccess10198Second5Observations,
    writeSuccess10198MiddleFirstObservations,
    writeSuccess10198MiddleSecondObservations,
    writeSuccess10198SuffixFirstObservations,
    writeSuccess10198SuffixMiddleObservations,
    writeSuccess10198SuffixObservations. cbn. reflexivity.
Qed.

Print Assumptions segment_10198_covered.
