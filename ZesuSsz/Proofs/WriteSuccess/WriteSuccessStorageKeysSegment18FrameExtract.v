From Coq Require Import Lists.List ZArith.ZArith.
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Contracts.IslarisMachine.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessLoopCommon.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessStorageKeysSpec.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessStorageKeysSegment18FrameDefs.

Lemma write_success_storage_keys_segment18_extract
    `{!islaG Sigma} `{!threadG} (x19 : bv 64) (P : iProp Sigma) :
  writeSuccessStorageKeysLoopSpec x19 P -∗
  writeSuccessStorageKeysLbuPrepared x19 P.
Proof.
  iIntros "Hentry".
  rewrite /writeSuccessStorageKeysLoopSpec.
  iDestruct "Hentry" as
    (sp pointer base total processed remaining bytes tail)
    "(Hsys & Hother & Hx19 & Hx2 & Hx22 & Hx27 & Harray & Hscratch & Hmmio &
      Hevents & HP & Hinv & Hexit & _)".
  iDestruct (reg_col_lookup writeSuccessStorageKeysOtherRegShapes 0%nat
    (KindReg "x1", BitsShape 64) with "Hother") as
    (old Hshape) "(Htarget & Hother)".
  { vm_compute. reflexivity. }
  apply valu_has_bits_shape in Hshape as (oldbv & ->).
  iAssert (("x1" ↦ᵣ: fun _ => True))%I with "[Htarget]" as "HtargetAny".
  { rewrite reg_mapsto_pred_eq /reg_mapsto_pred_def.
    iExists _. iSplit; first iExact "Htarget". done. }
  iPoseProof "Hinv" as "HinvCopy".
  iEval (rewrite /writeSuccessFixedWidthArrayInvariant) in "HinvCopy".
  iDestruct "HinvCopy" as
    "(%Htotal & %Hlength & %Hpointer & %HremainingBound & %HspAlign &
      %HspLower & %HspUpper & %HbaseLower & %HbaseUpper & _)".
  iAssert (writeSuccessFixedWidthArrayInvariant sp pointer base total
    processed remaining bytes)%I with "[]" as "Hinv".
  { rewrite /writeSuccessFixedWidthArrayInvariant.
    iSplit; first (iPureIntro; exact Htotal).
    iSplit; first (iPureIntro; exact Hlength).
    iSplit; first (iPureIntro; exact Hpointer).
    iSplit; first (iPureIntro; exact HremainingBound).
    iSplit; first (iPureIntro; exact HspAlign).
    iSplit; first (iPureIntro; exact HspLower).
    iSplit; first (iPureIntro; exact HspUpper).
    iSplit; first (iPureIntro; exact HbaseLower).
    iSplit; first (iPureIntro; exact HbaseUpper).
    done. }
  iAssert (writeSuccessStorageKeysLbuOuterFrame P x19 sp pointer base total
    processed remaining bytes tail)%I with
    "[Hx19 Hx2 Hx27 Hscratch Hmmio Hevents HP Hinv Hexit]" as "Houter".
  { rewrite /writeSuccessStorageKeysLbuOuterFrame.
    iSplitL "Hx19"; first iExact "Hx19".
    iSplitL "Hx2"; first iExact "Hx2".
    iSplitL "Hx27"; first iExact "Hx27".
    iSplitL "Hscratch"; first iExact "Hscratch".
    iSplitL "Hmmio"; first iExact "Hmmio".
    iSplitL "Hevents"; first iExact "Hevents".
    iSplitL "HP"; first iExact "HP".
    iSplitL "Hinv"; first iExact "Hinv".
    iSplitL "Hexit"; first iExact "Hexit".
    done. }
  have Hlength' : length bytes =
      (32 * (processed + S remaining))%nat by
    rewrite Htotal in Hlength; exact Hlength.
  rewrite /writeSuccessStorageKeysLbuPrepared.
  iExists sp, pointer, base, total, processed, remaining, bytes, tail.
  iSplitL "Hsys"; first iExact "Hsys".
  iSplitL "Hother"; first iExact "Hother".
  iSplitL "HtargetAny"; first iExact "HtargetAny".
  iSplitL "Hx22"; first iExact "Hx22".
  iSplitL "Harray"; first iExact "Harray".
  iSplitL "Houter"; first iExact "Houter".
  iSplit; first (iPureIntro; exact Hlength').
  iSplit; first (iPureIntro; exact Hpointer).
  iSplit; first (iPureIntro; exact HbaseLower).
  iPureIntro. exact HbaseUpper.
Qed.
