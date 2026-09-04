From Coq Require Import Lists.List ZArith.ZArith.
Require Import isla.riscv64.riscv64.
From IslaTraces.write_success_blocks Require Import Index.
Require Import ZesuSsz.Contracts.IslarisCode.
Require Import ZesuSsz.Experiments.WriteSuccessBlobHashesSegment15Frame.
Require Import ZesuSsz.Experiments.WriteSuccessBlobHashesSegment17IndexZeroSpec.

Lemma write_success_blob_hashes_segment17_core
    `{!islaG Sigma} `{!threadG} (P : iProp Sigma)
    (sp pointer : bv 64) (base : Z) (total processed remaining : nat)
    (bytes : list (bv 8)) (tail : spec) (byte : bv 8) :
  instr_lookup_resources IslaTraces.write_success_blocks.Index.lookup -∗
  instr_body 0x15490
    (writeSuccessBlobHashesLbuResult P "x21" 18 0 sp pointer base total
      processed remaining bytes tail byte) -∗
  instr_body 0x1548c (writeSuccessBlobHashesLbuState P "x21" 18 0 sp pointer
    base total processed remaining bytes tail byte).
Proof.
  iIntros "#Hlookup Hnext".
  iAssert (instr_pre 0x15490
    (writeSuccessBlobHashesLbuResult P "x21" 18 0 sp pointer base total
      processed remaining bytes tail byte))%I with "[Hnext]" as "HnextPre".
  { iApply instr_pre_to_body. iNext. iExact "Hnext". }
  iEval (rewrite /instr_lookup_resources) in "Hlookup".
  iPoseProof ("Hlookup" $! 0x1548c with "[]") as "#Hinstr1548c".
  { iPureIntro.
    rewrite IslaTraces.write_success_blocks.Index.lookup_a1548c.
    done. }
  iPoseProof (write_success_blob_hashes_a1548c_index_zero_spec 0x1548c with
    "Hinstr1548c") as "Hlbu".
  rewrite instr_pre'_eq. iIntros "Hstate".
  rewrite /writeSuccessBlobHashesLbuState.
  iDestruct "Hstate" as
    "(Hsys & Hother & Htarget & Hx19 & Hbyte & Hdone & Hprefix & Hsuffix &
      %HlookupByte & %Hpointer & %Hlower & %Hupper & Houter)".
  iEval (rewrite Z.add_0_r) in "Hbyte".
  iApply "Hlbu".
  rewrite /writeSuccessBlobHashesLbuIndexZeroSpec.
  iExists pointer, byte.
  iFrame "Hsys Htarget Hx19 Hbyte".
  iSplit; first (iPureIntro; lia).
  iSplit; last done.
  rewrite instr_pre'_eq. iNext. iIntros "Hpost".
  iDestruct "Hpost" as
    "(HsysPost & HtargetPost & Hx19Post & HbytePost & _)".
  iAssert ((bv_unsigned pointer + 0) ↦ₘ byte)%I with "[HbytePost]"
    as "HbyteResult".
  { rewrite Z.add_0_r. iExact "HbytePost". }
  iApply "HnextPre".
  rewrite /writeSuccessBlobHashesLbuResult.
  iFrame "HsysPost Hother HtargetPost Hx19Post HbyteResult Hdone Hprefix
    Hsuffix Houter".
  repeat iSplit; iPureIntro; assumption.
Qed.
