Require Import ZesuSsz.Automation.All.
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessCalls.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessTransactionsOptionalAddressSome1518cCallFrame.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessTransactionsOptionalAddressSome1518cCallEntry.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessTransactionsSpec.

Lemma write_success_transactions_optional_address_some_1518c_call_adapter
    `{!islaG Sigma} `{!threadG} (P : iProp Sigma)
    (sp : bv 64) (base : Z) (transaction : writeSuccessTransaction)
    (transactions processed remaining : list writeSuccessTransaction)
    (bytes prefix suffix : list (bv 8)) (tail : spec) :
  writeSuccessTransactionsOptionalAddressSome1518cCallFrame P sp base transaction
    transactions processed remaining bytes prefix suffix tail -∗
  zesuWriteOutputCallSpec.
Proof.
  iIntros "Hframe".
  iPoseProof (write_success_transactions_optional_address_some_1518c_call_frame
    P sp base transaction transactions processed remaining bytes prefix suffix tail
    with "Hframe") as "Hentry".
  iApply (write_success_transactions_optional_address_some_1518c_call_entry
    P sp base transaction transactions processed remaining bytes prefix suffix tail
    with "Hentry").
Qed.
