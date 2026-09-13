Require Import ZesuSsz.Automation.All.
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Contracts.IslarisMemory.

Lemma test_byte_array_word_region `{!islaG Sigma}
    (address : Z) (bytes : list (bv 8)) (Hlength : length bytes = 848%nat) :
  address ↦ₘ∗ bytes -∗
  address ↦ₘ∗ take 720 bytes ∗
  (address + 720) ↦ₘ∗ u64s_of_bytes 16 (take 128 (drop 720 bytes)) ∗
  (address + 848) ↦ₘ∗ drop 848 bytes.
Proof.
  iStartProof. iIntros "Hbytes".
  iApply (zesu_byte_array_word_region address (DfracOwn 1) bytes 720 16
    with "Hbytes"). lia.
Qed.

Print Assumptions test_byte_array_word_region.
