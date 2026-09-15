Require Import ZesuSsz.Automation.All.
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessOutputSemantic.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessPostTransactionResources.

Lemma descriptor_pure_resource `{!islaG Sigma}
    (descriptor : WriteOutputDescriptor) (bytes : list (bv 8)) :
  writeSuccessDescriptorResources descriptor bytes -∗
  ⌜bv_unsigned descriptor.2 = Z.of_nat (length bytes)⌝%I.
Proof.
  iStartProof. iIntros "Hdescriptor".
  zesu_extract_matching_descriptor_pure. zesu_run.
Qed.
Print Assumptions descriptor_pure_resource.

Lemma descriptor_pure_keeps_array `{!islaG Sigma}
    (descriptor : WriteOutputDescriptor) (bytes : list (bv 8)) :
  writeSuccessDescriptorResources descriptor bytes -∗
  ⌜bv_unsigned descriptor.2 = Z.of_nat (length bytes)⌝ ∗
  bv_unsigned descriptor.1 ↦ₘ∗ bytes.
Proof.
  iStartProof. iIntros "Hdescriptor".
  zesu_extract_matching_descriptor_pure. zesu_run.
Qed.
Print Assumptions descriptor_pure_keeps_array.
