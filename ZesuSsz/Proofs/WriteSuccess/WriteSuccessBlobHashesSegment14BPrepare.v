Require Import ZesuSsz.Automation.All.
From Coq Require Import Lists.List ZArith.ZArith.
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessBlobHashesSpec.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessBlobHashesSegment15Frame.

Lemma write_success_blob_hashes_segment14b_prepare
    `{!islaG Sigma} `{!threadG} (P : iProp Sigma) :
  writeSuccessBlobHashesLbuEntry P -∗
  ∃ (sp pointer : bv 64) (base : Z)
      (total processed remaining : nat) (bytes : list (bv 8))
      (tail : spec) (byte : bv 8),
    writeSuccessBlobHashesLbuState P "x9" 7 9 sp pointer base total
      processed remaining bytes tail byte.
Proof.
  iIntros "Hentry".
  rewrite /writeSuccessBlobHashesLbuEntry.
  iDestruct "Hentry" as
    (sp pointer base total processed remaining bytes tail)
    "(Hsys & Hother & Hx19 & Harray & Houter & %Hlength & %Hpointer &
      %HbaseLower & %HbaseUpper)".
  iDestruct (reg_col_lookup writeSuccessBlobHashesBodyOtherRegShapes 7%nat
    (KindReg "x9", BitsShape 64) with "Hother") as
    (old Hshape) "(Htarget & Hother)".
  { vm_compute. reflexivity. }
  apply valu_has_bits_shape in Hshape as (oldbv & ->).
  iAssert (("x9" ↦ᵣ: fun _ => True))%I with "[Htarget]" as "HtargetAny".
  { rewrite reg_mapsto_pred_eq /reg_mapsto_pred_def.
    iExists _. iSplit; first iExact "Htarget". done. }
  iPoseProof (write_success_blob_hashes_prepare_lbu_array pointer base
    processed remaining 9 bytes ltac:(lia) with
    "Harray [] [] [] []") as (byte)
    "(Hbyte & Hdone & Hprefix & Hsuffix & %Hlookup & %Hlower & %Hupper)".
  { iPureIntro. exact Hlength. }
  { iPureIntro. exact Hpointer. }
  { iPureIntro. exact HbaseLower. }
  { iPureIntro. exact HbaseUpper. }
  iExists sp, pointer, base, total, processed, remaining, bytes, tail, byte.
  rewrite /writeSuccessBlobHashesLbuState.
  iFrame "Hsys Hother HtargetAny Hx19 Hbyte Hdone Hprefix Hsuffix Houter".
  repeat iSplit; iPureIntro; assumption.
Qed.
