Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Experiments.WriteSuccessBlobHashesSpec.
Require Import ZesuSsz.Experiments.WriteSuccessBlobHashesSegment15Frame.

Lemma write_success_blob_hashes_chunk2a_registers_x23
    `{!islaG Sigma} `{!threadG} (byte : bv 8) :
  reg_col (delete 20%nat writeSuccessBlobHashesBodyOtherRegShapes) -∗
  "x23" ↦ᵣ RVal_Bits (bv_zero_extend 64 byte) -∗
  reg_col writeSuccessBlobHashesBodyOtherRegShapes.
Proof.
  iIntros "Hregs Hx23".
  rewrite (reg_col_lookup writeSuccessBlobHashesBodyOtherRegShapes 20%nat
    (KindReg "x23", BitsShape 64) ltac:(vm_compute; reflexivity)).
  iExists (RVal_Bits (bv_zero_extend 64 byte)).
  iSplit; first done. iFrame.
Qed.

Lemma write_success_blob_hashes_chunk2a_return_15494
    `{!islaG Sigma} `{!threadG} (P : iProp Sigma)
    (sp pointer : bv 64) (base : Z) (total processed remaining : nat)
    (bytes : list (bv 8)) (tail : spec) (byte : bv 8) :
  writeSuccessBlobHashesLbuResult P "x23" 20 2 sp pointer base total
    processed remaining bytes tail byte -∗ writeSuccessBlobHashesBodySpec P.
Proof.
  iIntros "Hstate". rewrite /writeSuccessBlobHashesLbuResult.
  iDestruct "Hstate" as
    "(Hsys & Hother & Hx23 & Hx19 & Hbyte & Hdone & Hprefix & Hsuffix &
      %Hlookup & %Hpointer & Houter)".
  iPoseProof (write_success_blob_hashes_segment15_recombine_lbu pointer base
    processed 2 bytes byte with "[] [] Hdone Hbyte Hprefix Hsuffix") as "Harray".
  { iPureIntro. exact Hpointer. }
  { iPureIntro. exact Hlookup. }
  iPoseProof (write_success_blob_hashes_chunk2a_registers_x23 byte with
    "Hother Hx23") as "Hother".
  iEval (unfold writeSuccessBlobHashesLbuOuterFrame) in "Houter".
  iDestruct "Houter" as
    "(Hx2 & Hx27 & Hscratch & Hmmio & Hevents & HP & Hinv & Hexit & _)".
  rewrite /writeSuccessBlobHashesBodySpec.
  iExists sp, pointer, base, total, processed, remaining, bytes, tail.
  iFrame.
Qed.
