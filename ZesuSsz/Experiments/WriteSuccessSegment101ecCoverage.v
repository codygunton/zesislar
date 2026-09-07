Require Import isla.riscv64.riscv64.
Require Import IslaTraces.write_success_02.a101ec.
Require Import IslaTraces.write_success_02.a101f0.
Require Import ZesuSsz.Contracts.InstructionBoundary.
Require Import ZesuSsz.Experiments.WriteSuccessTraceAssumptions.
Require Import ZesuSsz.Experiments.WriteSuccessSegment101ec.
Require Import ZesuSsz.Experiments.WriteSuccessSegment101ecCoveragePrefix.
Require Import ZesuSsz.Experiments.WriteSuccessSegment101ecCoverageSuffix.

Lemma writeSuccess101ecObservationsSplit regs global sp :
  writeSuccess101ecObservations regs global sp =
  writeSuccess101ecFirst5Observations regs global sp ++
  writeSuccess101ecTailObservations regs global sp.
Proof.
  unfold writeSuccess101ecObservations,
    writeSuccess101ecFirst5Observations,
    writeSuccess101ecTailObservations,
    writeSuccess101ecPrefixObservations. cbn. reflexivity.
Qed.

Lemma segment_101ec_mstatus_covered (regs : reg_map) (global : seq_global_state)
    (sp : bv 64) oldX15 observations after :
  regs !! "PC" = Some (RVal_Bits (Z_to_bv 64 0x101ec)) ->
  regs !! "x15" = Some (RVal_Bits sp) ->
  regs !! "x15" = Some oldX15 ->
  global.(seq_instrs) !! Z_to_bv 64 0x101ec = Some a101ec ->
  global.(seq_instrs) !! Z_to_bv 64 0x101f0 = Some a101f0 ->
  eval_a_exp regs writeSuccess101ecMstatus = Some (Val_Bool true) ->
  IslaInstructionSegment (writeSuccess101ecBefore regs global)
    observations after ->
  after = writeSuccess101ecAfter regs global sp /\
  observations = writeSuccess101ecObservations regs global sp.
Proof.
  intros Hpc Hsp Hdest Hcode Hnext Hmstatus Hsegment.
  destruct (segment_101ec_prefix5_covered regs global sp observations after
    Hpc Hmstatus Hsegment) as
    (done & labels & spawned & prefix5 & Hprefix5 & Hnil & Hdone & Hend & Hobs).
  destruct (segment_101ec_suffix_covered regs global sp oldX15
    prefix5 done labels spawned after Hpc Hsp Hdest Hnext Hprefix5 Hnil Hdone)
    as (Hafter & Hsuffix).
  split; first exact Hafter.
  repeat rewrite <- app_assoc in Hobs. rewrite Hsuffix in Hobs.
  rewrite writeSuccess101ecObservationsSplit. exact Hobs.
Qed.

Lemma segment_101ec_covered (regs : reg_map) (global : seq_global_state)
    (sp : bv 64) oldX15 observations after :
  regs !! "PC" = Some (RVal_Bits (Z_to_bv 64 0x101ec)) ->
  regs !! "x15" = Some (RVal_Bits sp) ->
  regs !! "x15" = Some oldX15 ->
  global.(seq_instrs) !! Z_to_bv 64 0x101ec = Some a101ec ->
  global.(seq_instrs) !! Z_to_bv 64 0x101f0 = Some a101f0 ->
  writeSuccessTraceAssumptions (writeSuccess101ecBefore regs global) ->
  IslaInstructionSegment (writeSuccess101ecBefore regs global)
    observations after ->
  after = writeSuccess101ecAfter regs global sp /\
  observations = writeSuccess101ecObservations regs global sp.
Proof.
  intros Hpc Hsp Hdest Hcode Hnext Hassumptions Hsegment.
  eapply segment_101ec_mstatus_covered; eauto.
  exact (writeSuccess101ecMstatusFromTraceAssumptions regs global Hassumptions).
Qed.

Print Assumptions writeSuccess101ecObservationsSplit.
Print Assumptions segment_101ec_mstatus_covered.
Print Assumptions segment_101ec_covered.
