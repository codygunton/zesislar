Require Import ZesuSsz.Automation.All.
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessExactByteListsSpec.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessExactByteListsCall.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessExactByteListsAfterCall.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessExactEncoderBytes.
From IslaTraces.write_success_05 Require Import instrs.

Lemma byte_lists_exact_loop_correct `{!islaG Sigma} `{!threadG}
    (P : iProp Sigma) :
  ([∗ list] instruction ∈ IslaTraces.write_success_05.instrs.instr_map,
    instr instruction.1 (Some instruction.2))%I -∗
  □ instr_pre 0x15c6c encoderBytesExactCallSpec -∗
  □ instr_pre 0x15c3c (byteListsExactLoopSpec P) -∗
  instr_body 0x15c3c (byteListsExactLoopSpec P).
Proof.
  iStartProof. iIntros "#Hcode #Hencoder #Hloop".
  iApply (byte_lists_exact_call_correct with "Hcode Hencoder Hloop").
  iApply (byte_lists_exact_after_call_correct with "Hcode").
Qed.
Print Assumptions byte_lists_exact_loop_correct.

Lemma byte_lists_exact_loop_pre `{!islaG Sigma} `{!threadG}
    (P : iProp Sigma) :
  ([∗ list] instruction ∈ IslaTraces.write_success_05.instrs.instr_map,
    instr instruction.1 (Some instruction.2))%I -∗
  □ instr_pre 0x15c6c encoderBytesExactCallSpec -∗
  □ instr_pre 0x15c3c (byteListsExactLoopSpec P).
Proof.
  iStartProof. iIntros "#Hcode #Hencoder". iLöb as "IH".
  iModIntro. iApply instr_pre_to_body. iNext.
  iApply (byte_lists_exact_loop_correct with "Hcode Hencoder IH").
Qed.
Print Assumptions byte_lists_exact_loop_pre.
