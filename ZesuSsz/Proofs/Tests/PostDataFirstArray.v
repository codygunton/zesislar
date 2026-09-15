Require Import ZesuSsz.Automation.All.
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessPostTransactionDescriptors.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessPostTransactionResources.

Lemma post_data_first_descriptor_array `{!islaG Sigma} `{!threadG}
    (sp : bv 64) (sourceBytes decodedBytes : list (bv 8))
    (data : WriteSuccessPostTransactionData) (P : iProp Sigma) :
  writeSuccessPostTransactionDataResources sp sourceBytes decodedBytes data ∗ P -∗
  (bv_unsigned (writeSuccessPostBytes1571c data).1 ↦ₘ∗
    writeSuccessPostBytes1571cPayload data) ∗
  ⌜bv_unsigned (writeSuccessPostBytes1571c data).2 =
    Z.of_nat (length (writeSuccessPostBytes1571cPayload data))⌝ ∗ P.
Proof.
  iStartProof. iIntros "[Hpost HP]".
  zesu_open_requested_nested_array_package.
  zesu_open_resource_groups.
  iFrame "∗".
  zesu_run.
Qed.
Print Assumptions post_data_first_descriptor_array.
