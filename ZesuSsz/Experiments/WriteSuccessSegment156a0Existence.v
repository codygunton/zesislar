Require Import isla.riscv64.riscv64.
Require Import IslaTraces.write_success_90.a156a0.
Require Import IslaTraces.write_success_90.a156a4.
Require Import ZesuSsz.Contracts.InstructionBoundary.
Require Import ZesuSsz.Experiments.WriteSuccessSegmentAutomation.
Require Import ZesuSsz.Experiments.WriteSuccessSegment15694.
Require Import ZesuSsz.Experiments.WriteSuccessSegment156a0Defs.
Require Import ZesuSsz.Experiments.WriteSuccessSegment156a0ExistencePrefix.
Require Import ZesuSsz.Experiments.WriteSuccessSegment156a0ExistenceSuffix.

Lemma segment_156a0_mstatus (regs : reg_map) (global : seq_global_state) oldX1 :
  regs !! "PC" = Some (RVal_Bits (Z_to_bv 64 0x156a0)) ->
  regs !! "x1" = Some oldX1 ->
  global.(seq_instrs) !! Z_to_bv 64 0x156a0 = Some a156a0 ->
  global.(seq_instrs) !! Z_to_bv 64 0x156a4 = Some a156a4 ->
  eval_a_exp regs writeSuccess15694Mstatus = Some (Val_Bool true) ->
  IslaInstructionSegment (writeSuccess156a0Before regs global)
    (writeSuccess156a0Observations regs global)
    (writeSuccess156a0After regs global) /\
  (writeSuccess156a0After regs global).1.(seq_regs) =
    writeSuccess156a0Regs regs /\
  (writeSuccess156a0After regs global).2.(seq_mem) = global.(seq_mem) /\
  concat (map microLabels (writeSuccess156a0Observations regs global)) = [].
Proof.
  intros Hpc Hx1 Hcode Hnext Hmstatus.
  have Hprefix := segment_156a0_prefix_exists regs global Hpc Hmstatus.
  have Hsuffix := segment_156a0_suffix_exists regs global oldX1 Hpc Hx1.
  have Hpath := writeSuccess156a0PrefixPathAppend _ _ _ _ _ Hprefix Hsuffix.
  split; [|repeat split; reflexivity].
  unfold writeSuccess156a0Observations.
  rewrite writeSuccess156a0PrefixObservationsSplit.
  eapply islaInstructionSegmentIntro with
    (done := (writeSuccess15694Local tnil (writeSuccess156a0Regs regs), global))
    (labels := []) (spawned := []).
  - split; first reflexivity. exists (Z_to_bv 64 0x156a0), a156a0.
    cbn. rewrite Hpc Hcode. repeat split; reflexivity.
  - exact Hpath.
  - reflexivity.
  - apply writeSuccessSeqDoneTabled with (next := a156a4) (trace := a156a4).
    + reflexivity.
    + reflexivity.
    + constructor.
    + exists (Z_to_bv 64 0x156a4).
      unfold writeSuccess156a0Regs. rewrite lookup_insert.
      rewrite writeSuccess156a0NextPcExact Hnext.
      repeat split; reflexivity.
  - left. split; first reflexivity. exists (Z_to_bv 64 0x156a4), a156a4.
    cbn. unfold writeSuccess156a0Regs. rewrite lookup_insert.
    rewrite writeSuccess156a0NextPcExact Hnext.
    repeat split; reflexivity.
Qed.

Lemma segment_156a0 (regs : reg_map) (global : seq_global_state) oldX1 :
  regs !! "PC" = Some (RVal_Bits (Z_to_bv 64 0x156a0)) ->
  regs !! "x1" = Some oldX1 ->
  global.(seq_instrs) !! Z_to_bv 64 0x156a0 = Some a156a0 ->
  global.(seq_instrs) !! Z_to_bv 64 0x156a4 = Some a156a4 ->
  eval_a_exp regs writeSuccess15694Mstatus = Some (Val_Bool true) ->
  IslaInstructionSegment (writeSuccess156a0Before regs global)
    (writeSuccess156a0Observations regs global)
    (writeSuccess156a0After regs global) /\
  (writeSuccess156a0After regs global).1.(seq_regs) =
    writeSuccess156a0Regs regs /\
  (writeSuccess156a0After regs global).2.(seq_mem) = global.(seq_mem) /\
  concat (map microLabels (writeSuccess156a0Observations regs global)) = [].
Proof.
  intros Hpc Hx1 Hcode Hnext Hmstatus.
  eapply segment_156a0_mstatus; eauto.
Qed.

Print Assumptions segment_156a0_mstatus.
Print Assumptions segment_156a0.
Print Assumptions writeSuccess156a0RegsLookupOther.
Print Assumptions writeSuccess156a0RegsDom.
