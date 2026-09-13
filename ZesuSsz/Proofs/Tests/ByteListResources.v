Require Import ZesuSsz.Automation.All.
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Automation.ByteListResources.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessByteLists.

Lemma byte_list_processed_append `{!islaG Sigma} (address : Z)
    (done : list ByteListItem) (item : ByteListItem) :
  byteListProcessedResources address done -∗
  byteListItemResources (address + 16 * Z.of_nat (length done)) [item] -∗
  byteListProcessedResources address (done ++ [item]) ∗ True.
Proof.
  iStartProof. iIntros "Hdone (Hdata & Hsize & Hbytes & %Hlength & _)".
  zesu_run.
Qed.
Print Assumptions byte_list_processed_append.

Lemma byte_list_processed_return `{!islaG Sigma} (address : Z)
    (done : list ByteListItem) (item : ByteListItem) (P : iProp Sigma) :
  byteListProcessedResources address done -∗
  byteListItemResources (address + 16 * Z.of_nat (length done)) [item] -∗
  P -∗ byteListItemResources address (done ++ [item]) ∗ P ∗ True.
Proof.
  iStartProof. iIntros "Hdone (Hdata & Hsize & Hbytes & %Hlength & _) HP".
  zesu_run.
Qed.
Print Assumptions byte_list_processed_return.
