From Coq Require Import Lists.List ZArith.ZArith.
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Contracts.IslarisMachine.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessStorageKeysSpec.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessBlobHashesSegment15Frame.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessStorageKeysSegment18FrameDefs.

Lemma write_success_storage_keys_segment18_return
    `{!islaG Sigma} `{!threadG} (x19 : bv 64) (P : iProp Sigma)
    (sp pointer : bv 64) (base : Z) (total processed remaining : nat)
    (bytes : list (bv 8)) (tail : spec) (byte : bv 8) :
  reg_col zesu_ram_sys_regs -∗
  reg_col (delete 0%nat writeSuccessStorageKeysOtherRegShapes) -∗
  "x1" ↦ᵣ RVal_Bits (bv_zero_extend 64 byte) -∗
  "x22" ↦ᵣ RVal_Bits pointer -∗
  (bv_unsigned pointer + 3) ↦ₘ byte -∗
  base ↦ₘ∗ take (32 * processed) bytes -∗
  bv_unsigned pointer ↦ₘ∗ take 3 (drop (32 * processed) bytes) -∗
  (bv_unsigned pointer + 4) ↦ₘ∗ drop 4 (drop (32 * processed) bytes) -∗
  ⌜drop (32 * processed) bytes !! 3%nat = Some byte⌝ -∗
  ⌜bv_unsigned pointer = (base + 32 * Z.of_nat processed)%Z⌝ -∗
  writeSuccessStorageKeysLbuOuterFrame P x19 sp pointer base total processed
    remaining bytes tail -∗
  writeSuccessStorageKeysLoopSpec x19 P.
Proof.
  iIntros "Hsys Hother Hx1 Hx22 Hbyte Hdone Hprefix Hsuffix"
    (Hlookup Hpointer) "Houter".
  iPoseProof (write_success_blob_hashes_segment15_recombine_lbu pointer
    base processed 3 bytes byte with
    "[] [] Hdone Hbyte Hprefix Hsuffix") as "Harray".
  { iPureIntro. exact Hpointer. }
  { iPureIntro. exact Hlookup. }
  iAssert (reg_col writeSuccessStorageKeysOtherRegShapes)%I with
    "[Hother Hx1]" as "HotherFull".
  { rewrite (reg_col_lookup writeSuccessStorageKeysOtherRegShapes 0%nat
      (KindReg "x1", BitsShape 64) ltac:(vm_compute; reflexivity)).
    iExists (RVal_Bits (bv_zero_extend 64 byte)).
    iSplit; first done. iFrame. }
  iEval (unfold writeSuccessStorageKeysLbuOuterFrame) in "Houter".
  iDestruct "Houter" as
    "(Hx19 & H2 & H27 & Hscratch & Hmmio & Hevents & HP & Hinv & Hexit & _)".
  rewrite /writeSuccessStorageKeysLoopSpec.
  iExists sp, pointer, base, total, processed, remaining, bytes, tail.
  iFrame "Hsys HotherFull Hx19 Hx22 H2 H27 Harray Hscratch Hmmio Hevents HP Hinv
    Hexit".
Qed.
