Require Import ZesuSsz.Automation.AllLegacy.
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessBlobHashesSpec.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessBlobHashesSegment15Frame.

Lemma write_success_blob_hashes_chunk2a_registers_x26
    `{!islaG Sigma} `{!threadG} (byte : bv 8) :
  reg_col (delete 23%nat writeSuccessBlobHashesBodyOtherRegShapes) -∗
  "x26" ↦ᵣ RVal_Bits (bv_zero_extend 64 byte) -∗
  reg_col writeSuccessBlobHashesBodyOtherRegShapes.
Proof.
  iIntros "Hregs Hx26".
  rewrite (reg_col_lookup writeSuccessBlobHashesBodyOtherRegShapes 23%nat
    (KindReg "x26", BitsShape 64) ltac:(vm_compute; reflexivity)).
  iExists (RVal_Bits (bv_zero_extend 64 byte)).
  iSplit; first done. iFrame.
Qed.

Lemma write_success_blob_hashes_chunk2a_return_15498
    `{!islaG Sigma} `{!threadG} (P : iProp Sigma)
    (sp pointer : bv 64) (base : Z) (total processed remaining : nat)
    (bytes : list (bv 8)) (tail : spec) (byte : bv 8) :
  writeSuccessBlobHashesLbuResult P "x26" 23 3 sp pointer base total
    processed remaining bytes tail byte -∗ writeSuccessBlobHashesBodySpec P.
Proof.
  iIntros "Hstate". rewrite /writeSuccessBlobHashesLbuResult.
  iDestruct "Hstate" as
    "(Hsys & Hother & Hx26 & Hx19 & Hbyte & Hdone & Hprefix & Hsuffix &
      %Hlookup & %Hpointer & Houter)".
  iPoseProof (write_success_blob_hashes_segment15_recombine_lbu pointer base
    processed 3 bytes byte with "[] [] Hdone Hbyte Hprefix Hsuffix") as "Harray".
  { iPureIntro. exact Hpointer. }
  { iPureIntro. exact Hlookup. }
  iPoseProof (write_success_blob_hashes_chunk2a_registers_x26 byte with
    "Hother Hx26") as "Hother".
  iEval (unfold writeSuccessBlobHashesLbuOuterFrame) in "Houter".
  iDestruct "Houter" as
    "(Hx2 & Hx27 & Hscratch & Hmmio & Hevents & HP & Hinv & Hexit & _)".
  rewrite /writeSuccessBlobHashesBodySpec.
  iExists sp, pointer, base, total, processed, remaining, bytes, tail.
  iFrame.
Qed.
