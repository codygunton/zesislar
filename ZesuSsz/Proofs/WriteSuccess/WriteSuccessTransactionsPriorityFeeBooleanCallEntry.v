Require Import ZesuSsz.Automation.AllLegacy.
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessCallAbi.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessEncoderBooleanCall.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessTransactionsSpec.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessTransactionsPriorityFeeBooleanReturn.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessTransactionsPriorityFeeBooleanReturnPre.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessTransactionsPriorityFeeBooleanCallRet.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessTransactionsPriorityFeeBooleanAssemble.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessTransactionsPriorityFeeBooleanAbiTail.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessTransactionsPriorityFeeBooleanRegisters.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessTransactionsPriorityFeeCore.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessTransactionsPriorityFeeNoneBoundary.

Definition writeSuccessTransactionsPriorityFeeBooleanCallPreparedSpec
    `{!islaG Sigma} `{!threadG} (P : iProp Sigma) : iProp Sigma :=
  writeSuccessTransactionsPriorityFeeBooleanSetupSpec P
    (BV 64 0x15148) (fun _ => BV 64 0).

Global Instance : LithiumUnfold
  (@writeSuccessTransactionsPriorityFeeBooleanCallPreparedSpec) := I.

Lemma write_success_transactions_priority_fee_boolean_call_entry
    `{!islaG Sigma} `{!threadG} (P : iProp Sigma) :
  instr_body 0x15148 (writeSuccessTransactionsPriorityFeePostSpec P) -∗
  writeSuccessTransactionsPriorityFeeBooleanCallPreparedSpec P -∗
  zesuEncoderBooleanCallSpec.
Proof.
  iIntros "Hnext Hentry".
  iEval (unfold writeSuccessTransactionsPriorityFeeBooleanCallPreparedSpec)
    in "Hentry".
  iEval (unfold writeSuccessTransactionsPriorityFeeBooleanSetupSpec)
    in "Hentry".
  iDestruct "Hentry" as
    "(%sp & %base & %transaction & %transactions & %processed & %remaining &
      %bytes & %prefix & %suffix & %tail & Hsys & Htmp & Hcaller & Hsaved &
      H1 & H2 & H10 & H11 & Hstack & Hmmio & Htrace & Hframe & %Halign &
      %Hlower & %Hupper & _)".
  iPoseProof (write_success_transactions_priority_fee_boolean_return_pre P sp
    base transaction transactions processed remaining bytes prefix suffix tail
    with "Hnext Hframe") as "Hret".
  iAssert (writeSuccessTransactionsPriorityFeeBooleanRegisters
      transaction sp (BV 64 0x15148))%I
    with "[Hsys Htmp H10 H11 Hcaller Hsaved H1 H2]" as "Hregs".
  { rewrite /writeSuccessTransactionsPriorityFeeBooleanRegisters. iFrame. }
  iPoseProof (write_success_transactions_priority_fee_boolean_abi_tail
    transaction remaining sp tail Halign Hlower Hupper with
    "Hstack Hmmio Htrace Hret") as "Htail".
  iApply (write_success_transactions_priority_fee_boolean_assemble transaction
    remaining sp tail with "Hregs Htail").
Qed.
