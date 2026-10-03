Require Import ZesuSsz.Automation.All.
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessExactByteListsSpec.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessExactByteListsClosedCall.
From IslaTraces.write_success_05 Require Import instrs.
From IslaTraces.write_success_06 Require Import instrs.
From IslaTraces.write_success_07 Require Import instrs.
From IslaTraces.write_success_01 Require Import instrs.

(** The exact specification already uses zesu_call 80.
    Its trace contains the count payload and each item payload. *)
Definition encoderByteListsContract `{!islaG Sigma} `{!threadG} : iProp Sigma :=
  encoderByteListsExactCallSpec.
#[local] Instance : LithiumUnfold (@encoderByteListsContract) := I.
#[local] Typeclasses Opaque encoderByteListsContract.

Lemma encoder_byte_lists_contract_correct `{!islaG Sigma} `{!threadG} :
  ([∗ list] instruction ∈ IslaTraces.write_success_05.instrs.instr_map,
    instr instruction.1 (Some instruction.2))%I -∗
  ([∗ list] instruction ∈ IslaTraces.write_success_06.instrs.instr_map,
    instr instruction.1 (Some instruction.2))%I -∗
  ([∗ list] instruction ∈ IslaTraces.write_success_07.instrs.instr_map,
    instr instruction.1 (Some instruction.2))%I -∗
  ([∗ list] instruction ∈ IslaTraces.write_success_01.instrs.instr_map,
    instr instruction.1 (Some instruction.2))%I -∗
  instr_body 0x15c10 encoderByteListsContract.
Proof.
  iIntros "Hlists Hbytes Hint Houtput".
  rewrite /encoderByteListsContract -/zesuEncoderByteListsExactCallSpec.
  iApply (zesu_encoder_byte_lists_exact_call_correct with "Hlists Hbytes Hint Houtput").
Qed.
Print Assumptions encoder_byte_lists_contract_correct.
