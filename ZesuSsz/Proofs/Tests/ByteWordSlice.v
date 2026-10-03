Require Import ZesuSsz.Automation.All.
Require Import ZesuSsz.Automation.ByteWordSlice.
Require Import ZesuSsz.Automation.InteriorByteSlice.
Require Import ZesuSsz.Automation.SealedCoverage.
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Contracts.IslarisMemory.
#[local] Instance : ZesuSsz.Automation.ByteWordSlice.ZesuStepByteWordSlice := I.
Lemma byte_word_existential_tail `{!islaG Sigma} (base : Z) (bytes : list (bv 8)) (Hlength : length bytes = 848%nat) :
 base ↦ₘ∗ bytes -∗
 ∃ x : list (bv 64) *ₗ (), (base + 720) ↦ₘ∗ x.1ₗ ∗
 ⌜length x.1ₗ = 16%nat⌝ ∗ ((base + 720) ↦ₘ∗ x.1ₗ -∗ base ↦ₘ∗ bytes).
Proof.
 iIntros "Hbytes". ZesuSsz.Automation.ByteWordSlice.zesu_lend_byte_word_existential.
 iSplit; first (iPureIntro; assumption). iAssumption.
Qed.
Print Assumptions byte_word_existential_tail.
Lemma test_byte_word_tail_lender `{!islaG Sigma}
    (base : Z) (bytes : list (bv 8)) (Hlength : length bytes = 848%nat) :
  base ↦ₘ∗ bytes -∗
  (base + 720) ↦ₘ∗ u64s_of_bytes 16 (take 128 (drop 720 bytes)) ∗
  ((base + 720) ↦ₘ∗ u64s_of_bytes 16 (take 128 (drop 720 bytes)) -∗
    base ↦ₘ∗ bytes).
Proof.
  iIntros "Hbytes".
  iApply (zesu_byte_array_lend_words base bytes 720 16 with "Hbytes"). lia.
Qed.

Lemma test_byte_word_tail_subsume `{!islaG Sigma}
    (base : Z) (bytes : list (bv 8)) (Hlength : length bytes = 848%nat) :
  ⊢ subsume (base ↦ₘ∗ bytes)
    (fun _ : unit => (base + 720) ↦ₘ∗
      u64s_of_bytes 16 (take 128 (drop 720 bytes)))
    (fun _ : unit => (base + 720) ↦ₘ∗
      u64s_of_bytes 16 (take 128 (drop 720 bytes)) -∗ base ↦ₘ∗ bytes).
Proof.
  iApply (subsume_byte_array_word_region unit base (base + 720)%Z bytes 720 16).
  iSplit; first done. iSplit; first (iPureIntro; lia).
  iExists tt. iSplit; first done. iIntros "Hrestore". iExact "Hrestore".
Qed.

Lemma test_byte_word_tail_tuple `{!islaG Sigma}
    (base : Z) (bytes : list (bv 8)) (Hlength : length bytes = 848%nat) :
  ⊢ subsume (base ↦ₘ∗ bytes)
    (fun x : list (bv 64) *ₗ () => (base + 720) ↦ₘ∗ x.1ₗ)
    (fun x : list (bv 64) *ₗ () =>
      ⌜x.1ₗ = u64s_of_bytes 16 (take 128 (drop 720 bytes))⌝ ∗
      ((base + 720) ↦ₘ∗ x.1ₗ -∗ base ↦ₘ∗ bytes)).
Proof.
  iStartProof. ZesuSsz.Automation.ByteWordSlice.zesu_lend_byte_words.
  iSplit; first done. iAssumption.
Qed.

Lemma byte_word_existential_preserves_unrelated `{!islaG Sigma}
    (base other : Z) (bytes unrelated : list (bv 8))
    (Hlength : length bytes = 848%nat) :
  base ↦ₘ∗ bytes -∗ other ↦ₘ∗ unrelated -∗
  ∃ x : list (bv 64) *ₗ (), (base + 720) ↦ₘ∗ x.1ₗ ∗
  ⌜length x.1ₗ = 16%nat⌝ ∗
  ((base + 720) ↦ₘ∗ x.1ₗ -∗ base ↦ₘ∗ bytes) ∗ other ↦ₘ∗ unrelated.
Proof.
  iIntros "Hbytes Hunrelated". ZesuSsz.Automation.ByteWordSlice.zesu_lend_byte_word_existential.
  iSplit; first (iPureIntro; assumption). iFrame "Hrestore Hunrelated".
Qed.
Lemma byte_word_existential_rejects_noncovering `{!islaG Sigma}
    (base : Z) (bytes : list (bv 8)) (Hlength : length bytes = 720%nat) :
  base ↦ₘ∗ bytes -∗ True.
Proof.
  iIntros "Hbytes".
  Fail (iAssert (∃ x : list (bv 64) *ₗ (), (base + 720) ↦ₘ∗ x.1ₗ ∗
    ⌜length x.1ₗ = 16%nat⌝)%I with "[Hbytes]" as "Himpossible";
    [zesu_lend_byte_word_existential |]).
  done.
Qed.

Lemma byte_word_existential_restores_array `{!islaG Sigma}
    (base : Z) (bytes : list (bv 8)) (Hlength : length bytes = 848%nat) :
  base ↦ₘ∗ bytes -∗
  ∃ x : list (bv 64) *ₗ (), (base + 720) ↦ₘ∗ x.1ₗ ∗
  ((base + 720) ↦ₘ∗ x.1ₗ -∗ base ↦ₘ∗ bytes ∗ True).
Proof.
  iIntros "Hbytes". ZesuSsz.Automation.ByteWordSlice.zesu_lend_byte_word_existential.
  iIntros "Hreturned". zesu_restore_interior_byte_slice.
  iFrame.
Qed.

Definition byteWordTestSeal `{!islaG Sigma} (base : Z) (bytes : list (bv 8)) :
    iProp Sigma := (base ↦ₘ∗ bytes ∗ True)%I.
Lemma byteWordTestSeal_unfold `{!islaG Sigma} (base : Z) (bytes : list (bv 8)) :
    byteWordTestSeal base bytes ⊣⊢ (base ↦ₘ∗ bytes ∗ True)%I.
Proof. done. Qed.
Global Opaque byteWordTestSeal.
Global Instance byteWordTestSeal_declared `{!islaG Sigma} `{!threadG}
    (base : Z) (bytes : list (bv 8)) :
    ZesuSealed (byteWordTestSeal base bytes) (base ↦ₘ∗ bytes ∗ True)%I
      [(base, base + Z.of_nat (length bytes))] [] :=
    byteWordTestSeal_unfold base bytes.
Lemma byte_word_declared_tail_has_no_orphan_witness `{!islaG Sigma} `{!threadG}
    (base : Z) (bytes : list (bv 8)) (Hlength : length bytes = 848%nat) :
  byteWordTestSeal base bytes -∗
  ∃ x : list (bv 64) *ₗ (), (base + 720) ↦ₘ∗ x.1ₗ ∗
  ((base + 720) ↦ₘ∗ x.1ₗ -∗ base ↦ₘ∗ bytes ∗ True).
Proof.
  iIntros "Hbytes".
  ZesuSsz.Automation.ByteWordSlice.zesu_open_byte_word_seal.
  ZesuSsz.Automation.ByteWordSlice.zesu_lend_byte_word_existential.
  iIntros "Hreturned". zesu_restore_interior_byte_slice.
  iFrame.
Qed.
