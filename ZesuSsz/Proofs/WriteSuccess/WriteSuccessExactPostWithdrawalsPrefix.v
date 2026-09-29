Require Import ZesuSsz.Automation.All.
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Contracts.Endpoints.
Require Import ZesuSsz.Proofs.WriteSuccess.Interfaces.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessNativeContract.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessRepresentation.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessExactPostWithdrawalsSplit.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessExactPostWithdrawalsBefore156f4.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessExactPostWithdrawalsFrom156f4.

Lemma write_success_exact_post_withdrawals_prefix
    `{!islaG Sigma} `{!threadG} {Decoded}
    `{!WriteSuccessMemoryRepresentation Decoded}
    (args : WriteSuccessArgs Decoded)
    (witness : writeSuccessNativeWitness Decoded) (P : iProp Sigma)
    (Hwf : writeSuccessWitnessWellFormed args witness) :
  instr_lookup_resources IslaTraces.write_success_blocks.Index.lookup -∗
  IslaTraces.write_success_blocks.Index.spec_instr_resources -∗
  □ instr_pre 0x15d10 encoderIntEntryBoundary -∗
  instr_body 0x156fc (writeSuccessExactPostWithdrawalsAt156fc args witness P) -∗
  instr_body 0x156e8
    (writeSuccessExactPostWithdrawalsBoundary
      (writeSuccessFrameSp witness)
      (bv_unsigned (writeSuccessWithdrawalsBase witness))
      (writeSuccessWithdrawalsBytes witness)
      (writeSuccessExactPostWithdrawalsEvents witness)
      (writeSuccessExactPostWithdrawalsCallerFrame args witness ∗ P)).
Proof.
  iIntros "#Hlookup #Hspec #Hencoder Hnext".
  iApply (write_success_exact_post_withdrawals_before156f4 args witness P Hwf
    with "Hlookup Hspec Hencoder").
  iApply (write_success_exact_post_withdrawals_from156f4 args witness P Hwf
    with "Hlookup Hspec Hnext").
Qed.
Print Assumptions write_success_exact_post_withdrawals_prefix.
