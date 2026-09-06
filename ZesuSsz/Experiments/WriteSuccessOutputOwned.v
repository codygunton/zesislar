From Coq Require Import Lists.List ZArith.ZArith.
Require Import isla.riscv64.riscv64.
From IslaTraces.write_success_01 Require Import instrs.
Require Import ZesuSsz.Experiments.WriteSuccessOutput.
Require Import ZesuSsz.Experiments.WriteSuccessHostObservation.

Definition writeOutputConcreteExecutionEntry
    (initialLocal : seq_local_state) (initialState : seq_global_state)
    (data size ret : bv 64) : Prop :=
  initialLocal.(seq_trace) = tnil /\
  initialLocal.(seq_nb_state) = false /\
  initialLocal.(seq_pc_reg) = arch_pc_reg /\
  initialLocal.(seq_regs) !! arch_pc_reg =
    Some (RVal_Bits (BV 64 0x10190)) /\
  initialLocal.(seq_regs) !! "x1" = Some (RVal_Bits ret) /\
  initialLocal.(seq_regs) !! "x10" = Some (RVal_Bits data) /\
  initialLocal.(seq_regs) !! "x11" = Some (RVal_Bits size) /\
  initialState.(seq_instrs) !! (BV 64 0x10190) = Some a10190.

Definition WriteSuccessOutputHelperEventState
    (initialLocal : seq_local_state) (initialState : seq_global_state)
    (eventIndex : nat) (eventLocal : seq_local_state)
    (eventState : seq_global_state)
    (data size ret : bv 64) : Prop :=
  writeOutputConcreteExecutionEntry initialLocal initialState data size ret /\
  WriteSuccessOutputEventState initialLocal initialState eventIndex
    eventLocal eventState data.

Definition WriteSuccessOutputHelperExecutionObservation
    (initialLocal : seq_local_state) (initialState : seq_global_state)
    (eventIndex : nat) (eventLocal : seq_local_state)
    (eventState : seq_global_state)
    (data size ret : bv 64) (payload : list (bv 8)) : Prop :=
  WriteSuccessOutputHelperEventState initialLocal initialState eventIndex
    eventLocal eventState data size ret /\
  WriteSuccessHostObservation eventState.(seq_mem)
    eventIndex data size payload.

Lemma write_output_owned_payload_correct
    `{!islaG Sigma} `{!threadG}
    (data size ret : bv 64) (payload : list (bv 8)) (P : iProp Sigma) :
  ([∗ list] instruction ∈ IslaTraces.write_success_01.instrs.instr_map,
    instr instruction.1 (Some instruction.2))%I -∗
  instr_body 0x10190
    (writeOutputEntry data size ret
      (bv_unsigned data ↦ₘ∗ payload ∗ P) ∗
     instr_pre (bv_unsigned ret)
      (writeOutputExit data size ret
        (bv_unsigned data ↦ₘ∗ payload ∗ P)) ∗ True).
Proof.
  iIntros "#Hcode".
  iApply (write_output_correct data size ret
    (bv_unsigned data ↦ₘ∗ payload ∗ P) with "Hcode").
Qed.

Definition writeOutputOwnedExecutionObservation
    `{!islaG Sigma} `{!threadG}
    (initialLocal eventLocal : seq_local_state)
    (initialState eventState : seq_global_state)
    (labels : list seq_label) (eventIndex : nat)
    (data size ret : bv 64) (payload : list (bv 8))
    (tail : spec) (P : iProp Sigma) : iProp Sigma :=
  (instr_body 0x10190
      (writeOutputTraceSpec data size ret tail
        (bv_unsigned data ↦ₘ∗ payload ∗ P)) ∗
   (state_ctx eventState labels ∗ bv_unsigned data ↦ₘ∗ payload -∗
      ⌜WriteSuccessOutputHelperExecutionObservation
        initialLocal initialState eventIndex eventLocal eventState
        data size ret payload⌝ ∗
      state_ctx eventState labels ∗ bv_unsigned data ↦ₘ∗ payload))%I.

Lemma write_output_owned_payload_execution_observed_trace_correct
    `{!islaG Sigma} `{!threadG}
    (initialLocal eventLocal : seq_local_state)
    (initialState eventState : seq_global_state)
    (labels : list seq_label) (eventIndex : nat)
    (data size ret : bv 64) (payload : list (bv 8))
    (tail : spec) (P : iProp Sigma) :
  WriteSuccessOutputHelperEventState initialLocal initialState eventIndex
    eventLocal eventState data size ret ->
  bv_unsigned size = Z.of_nat (length payload) ->
  ([∗ list] instruction ∈ IslaTraces.write_success_01.instrs.instr_map,
    instr instruction.1 (Some instruction.2))%I -∗
  writeOutputOwnedExecutionObservation
    initialLocal eventLocal initialState eventState labels eventIndex
    data size ret payload tail P.
Proof.
  iIntros ([Hentry Hevent] Hsize) "#Hcode".
  rewrite /writeOutputOwnedExecutionObservation.
  iSplitL.
  - iApply (write_output_trace_correct data size ret tail
      (bv_unsigned data ↦ₘ∗ payload ∗ P) with "Hcode").
  - iIntros "[Hstate Hpayload]".
    iAssert ⌜WriteSuccessExecutionHostObservation
      initialLocal initialState eventIndex eventLocal eventState
      data size payload⌝%I as %Hobservation.
    { iApply (writeSuccessOwnedExecutionPayloadObservation
        initialLocal eventLocal initialState eventState labels eventIndex
        data size payload Hevent Hsize with "Hstate Hpayload"). }
    destruct Hobservation as [_ Hobservation].
    iFrame. iPureIntro. split; [split; done | exact Hobservation].
Qed.

Lemma write_output_owned_payload_trace_correct
    `{!islaG Sigma} `{!threadG}
    (data size ret : bv 64) (payload : list (bv 8))
    (tail : spec) (P : iProp Sigma) :
  ([∗ list] instruction ∈ IslaTraces.write_success_01.instrs.instr_map,
    instr instruction.1 (Some instruction.2))%I -∗
  instr_body 0x10190
    (writeOutputTraceSpec data size ret tail
      (bv_unsigned data ↦ₘ∗ payload ∗ P)).
Proof.
  iIntros "#Hcode".
  iApply (write_output_trace_correct data size ret tail
    (bv_unsigned data ↦ₘ∗ payload ∗ P) with "Hcode").
Qed.
