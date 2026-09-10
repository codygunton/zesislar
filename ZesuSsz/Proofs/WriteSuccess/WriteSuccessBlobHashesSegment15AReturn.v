From Coq Require Import Lists.List ZArith.ZArith.
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Contracts.IslarisMachine.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessBlobHashesSpec.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessBlobHashesSegment15Frame.

Lemma write_success_blob_hashes_segment15a_return
    `{!islaG Sigma} `{!threadG} (P : iProp Sigma)
    (sp pointer : bv 64) (base : Z) (total processed remaining : nat)
    (bytes : list (bv 8)) (tail : spec) (byte : bv 8) :
  reg_col zesu_ram_sys_regs -∗
  reg_col (delete 16%nat writeSuccessBlobHashesBodyOtherRegShapes) -∗
  "x18" ↦ᵣ RVal_Bits (bv_zero_extend 64 byte) -∗
  "x19" ↦ᵣ RVal_Bits pointer -∗
  (bv_unsigned pointer + 10) ↦ₘ byte -∗
  base ↦ₘ∗ take (32 * processed) bytes -∗
  bv_unsigned pointer ↦ₘ∗ take 10 (drop (32 * processed) bytes) -∗
  (bv_unsigned pointer + 11) ↦ₘ∗
    drop 11 (drop (32 * processed) bytes) -∗
  ⌜drop (32 * processed) bytes !! 10%nat = Some byte⌝ -∗
  ⌜bv_unsigned pointer = (base + 32 * Z.of_nat processed)%Z⌝ -∗
  writeSuccessBlobHashesLbuOuterFrame P sp pointer base total processed
    remaining bytes tail -∗
  writeSuccessBlobHashesBodySpec P.
Proof.
  iIntros "Hsys Hother Hx18 Hx19 Hbyte Hdone Hprefix Hsuffix"
    (Hlookup Hpointer) "Houter".
  iPoseProof (write_success_blob_hashes_segment15_recombine_lbu pointer
    base processed 10 bytes byte with
    "[] [] Hdone Hbyte Hprefix Hsuffix") as "Harray".
  { iPureIntro. exact Hpointer. }
  { iPureIntro. exact Hlookup. }
  iPoseProof (write_success_blob_hashes_segment15_registers_x18 byte with
    "Hother Hx18") as "Hother".
  iEval (unfold writeSuccessBlobHashesLbuOuterFrame) in "Houter".
  iDestruct "Houter" as
    "(Hx2 & Hx27 & Hscratch & Hmmio & Hevents & HP & Hinv & Hexit & _)".
  rewrite /writeSuccessBlobHashesBodySpec.
  iExists sp, pointer, base, total, processed, remaining, bytes, tail.
  iFrame "Hsys Hother Hx19 Harray Hx2 Hx27 Hscratch Hmmio Hevents HP Hinv
    Hexit".
Qed.
