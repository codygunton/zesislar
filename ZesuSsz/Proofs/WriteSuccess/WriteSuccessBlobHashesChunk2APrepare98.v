Require Import ZesuSsz.Automation.All.
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessBlobHashesSpec.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessBlobHashesSegment15Frame.

Lemma write_success_blob_hashes_chunk2a_prepare_15498 `{!islaG Sigma}
    `{!threadG} (P : iProp Sigma) :
  writeSuccessBlobHashesLbuEntry P -∗
  ∃ (sp pointer : bv 64) (base : Z) (total processed remaining : nat)
      (bytes : list (bv 8)) (tail : spec) (byte : bv 8),
    writeSuccessBlobHashesLbuState P "x26" 23 3 sp pointer base total
      processed remaining bytes tail byte.
Proof.
  iIntros "Hentry".
  rewrite /writeSuccessBlobHashesLbuEntry.
  iDestruct "Hentry" as
    (sp pointer base total processed remaining bytes tail)
    "(Hsys & Hother & Hx19 & Harray & Houter & %Hlength & %Hpointer &
      %HbaseLow & %HbaseHigh)".
  iDestruct (reg_col_lookup writeSuccessBlobHashesBodyOtherRegShapes 23%nat
    (KindReg "x26", BitsShape 64) with "Hother") as
    (old Hshape) "(Htarget & Hother)".
  { vm_compute. reflexivity. }
  apply valu_has_bits_shape in Hshape as (oldbv & ->).
  iAssert (("x26" ↦ᵣ: fun _ => True))%I with "[Htarget]" as "Htarget".
  { rewrite reg_mapsto_pred_eq /reg_mapsto_pred_def.
    iExists _. iSplit; first iExact "Htarget". done. }
  iPoseProof (write_success_blob_hashes_prepare_lbu_array pointer base
    processed remaining 3 bytes ltac:(lia) with "Harray [] [] [] []") as
    "Hprepared".
  { iPureIntro. exact Hlength. }
  { iPureIntro. exact Hpointer. }
  { iPureIntro. exact HbaseLow. }
  { iPureIntro. exact HbaseHigh. }
  iDestruct "Hprepared" as
    (byte) "(Hbyte & Hdone & Hprefix & Hsuffix & %Hlookup & %Hlower & %Hupper)".
  iExists sp, pointer, base, total, processed, remaining, bytes, tail, byte.
  rewrite /writeSuccessBlobHashesLbuState.
  iFrame "Hsys Hother Htarget Hx19 Hbyte Hdone Hprefix Hsuffix Houter".
  repeat iSplit; try iPureIntro; try assumption; done.
Qed.
