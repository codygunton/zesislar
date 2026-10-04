Require Import ZesuSsz.Automation.All.
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Automation.ByteListResources.
Require Import ZesuSsz.Automation.ByteLists.

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

Lemma byte_list_processed_identity `{!islaG Sigma} (address : Z)
    (items : list ByteListItem) (P : iProp Sigma) :
  byteListProcessedResources address items -∗
  P -∗ byteListItemResources address items ∗ P ∗ True.
Proof.
  iStartProof. iIntros "Hitems HP".
  zesu_open_processed_resources. zesu_run.
Qed.
Print Assumptions byte_list_processed_identity.

Lemma byte_list_processed_empty `{!islaG Sigma} (address : Z)
    (P : iProp Sigma) :
  P -∗ byteListProcessedResources address [] ∗ P ∗ True.
Proof.
  iStartProof. iIntros "HP". zesu_run.
Qed.
Print Assumptions byte_list_processed_empty.
