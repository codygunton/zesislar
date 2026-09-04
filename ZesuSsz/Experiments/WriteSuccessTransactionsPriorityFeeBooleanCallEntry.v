Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Experiments.WriteSuccessCallAbi.
Require Import ZesuSsz.Experiments.WriteSuccessEncoderBooleanCall.
Require Import ZesuSsz.Experiments.WriteSuccessTransactionsSpec.
Require Import ZesuSsz.Experiments.WriteSuccessTransactionsPriorityFeeBooleanReturn.
Require Import ZesuSsz.Experiments.WriteSuccessTransactionsPriorityFeeBooleanReturnPre.
Require Import ZesuSsz.Experiments.WriteSuccessTransactionsPriorityFeeBooleanCallRet.
Require Import ZesuSsz.Experiments.WriteSuccessTransactionsPriorityFeeBooleanAssemble.
Require Import ZesuSsz.Experiments.WriteSuccessTransactionsPriorityFeeBooleanAbiTail.
Require Import ZesuSsz.Experiments.WriteSuccessTransactionsPriorityFeeBooleanRegisters.
Require Import ZesuSsz.Experiments.WriteSuccessTransactionsPriorityFeeCore.
Require Import ZesuSsz.Experiments.WriteSuccessTransactionsPriorityFeeNoneBoundary.

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
