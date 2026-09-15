Require Import ZesuSsz.Automation.All.
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessExactValueSpec.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessNativeContract.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessOutputSemantic.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessPostTransactionResources.

Lemma exact_hash_array_pair `{!islaG Sigma} {Decoded}
    (witness : writeSuccessNativeWitness Decoded)
    (dropBytes : list (bv 8)) (P : iProp Sigma) :
  ((bv_unsigned (writeSuccessFrameSp witness) + 1588) ↦ₘ∗
     writeSuccessValueBlockHash (writeSuccessValues witness) ∗
   (bv_unsigned (writeSuccessFrameSp witness) + 1620) ↦ₘ∗ dropBytes) ∗ P -∗
  (bv_unsigned (writeSuccessFrameSp witness) + 1588) ↦ₘ∗
    writeSuccessValueBlockHash (writeSuccessValues witness) ∗
  (bv_unsigned (writeSuccessFrameSp witness) + 1620) ↦ₘ∗ dropBytes ∗ P.
Proof.
  iStartProof. iIntros "Howners".
  iDestruct "Howners" as "[? HP]".
  zesu_open_requested_exact_array_pair.
  iFrame "∗".
Qed.
Print Assumptions exact_hash_array_pair.

Lemma exact_array_pair_skips_other_owner `{!islaG Sigma}
    (other base : Z) (left right hash dropBytes : list (bv 8))
    (P : iProp Sigma) :
  ((other ↦ₘ∗ left ∗ (other + Z.of_nat (length left)) ↦ₘ∗ right) ∗
   (base ↦ₘ∗ hash ∗ (base + Z.of_nat (length hash)) ↦ₘ∗ dropBytes) ∗ P) -∗
  base ↦ₘ∗ hash ∗ (base + Z.of_nat (length hash)) ↦ₘ∗ dropBytes ∗
  other ↦ₘ∗ left ∗ (other + Z.of_nat (length left)) ↦ₘ∗ right ∗ P.
Proof.
  iStartProof. iIntros "Howners".
  iDestruct "Howners" as "[? [? HP]]".
  zesu_open_requested_exact_array_pair.
  iFrame "∗".
Qed.
Print Assumptions exact_array_pair_skips_other_owner.

Lemma descriptor_exact_array_pure_bundle `{!islaG Sigma}
    (descriptor : WriteOutputDescriptor) (bytes : list (bv 8))
    (P : iProp Sigma) :
  writeSuccessDescriptorResources descriptor bytes ∗ P -∗
  (bv_unsigned descriptor.1 ↦ₘ∗ bytes ∗
   ⌜bv_unsigned descriptor.2 = Z.of_nat (length bytes)⌝) ∗ P.
Proof.
  iStartProof. iIntros "Howners".
  iDestruct "Howners" as "[? HP]".
  zesu_open_matching_array_pure_bundle.
  iFrame "∗".
  zesu_run.
Qed.
Print Assumptions descriptor_exact_array_pure_bundle.

Lemma hashes_exact_array_pure_bundle `{!islaG Sigma}
    (pointer : bv 64) (count : nat) (bytes : list (bv 8))
    (P : iProp Sigma) :
  writeSuccessHashesResources pointer count bytes ∗ P -∗
  (bv_unsigned pointer ↦ₘ∗ bytes ∗
   ⌜length bytes = (32 * count)%nat⌝) ∗ P.
Proof.
  iStartProof. iIntros "Howners".
  iDestruct "Howners" as "[? HP]".
  zesu_open_matching_array_pure_bundle.
  iFrame "∗".
  zesu_run.
Qed.
Print Assumptions hashes_exact_array_pure_bundle.
