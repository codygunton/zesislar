Require Import ZesuSsz.Automation.AllLegacy.
Require Import isla.riscv64.riscv64.
Require Import InstrSpecs.Specs.
From IslaTraces.write_success_blocks Require Import Index.
Require Import IslaTraces.write_success_67.a15490_spec.
Require Import ZesuSsz.Contracts.IslarisCode.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessBlobHashesSegment15Frame.

Local Remove Hints a15490_spec_inst : typeclass_instances.

Lemma write_success_blob_hashes_segment17_core_15490
    `{!islaG Sigma} `{!threadG} (P : iProp Sigma)
    (sp pointer : bv 64) (base : Z) (total processed remaining : nat)
    (bytes : list (bv 8)) (tail : spec) (byte : bv 8) :
  instr_lookup_resources IslaTraces.write_success_blocks.Index.lookup -∗
  instr_body 0x15494
    (writeSuccessBlobHashesLbuResult P "x22" 19 1 sp pointer base total
      processed remaining bytes tail byte) -∗
  instr_body 0x15490 (writeSuccessBlobHashesLbuState P "x22" 19 1 sp
    pointer base total processed remaining bytes tail byte).
Proof.
  iIntros "#Hlookup Hnext".
  iEval (rewrite /instr_lookup_resources) in "Hlookup".
  iPoseProof ("Hlookup" $! 0x15490 with "[]") as "#Hinstr15490".
  { iPureIntro. rewrite IslaTraces.write_success_blocks.Index.lookup_a15490.
    done. }
  iPoseProof (a15490_spec 0x15490 with "Hinstr15490") as "Hbody".
  rewrite instr_pre'_eq. iIntros "Hstate".
  rewrite /writeSuccessBlobHashesLbuState.
  iDestruct "Hstate" as
    "(Hsys & Hother & Htarget & Hx19 & Hbyte & Hdone & Hprefix & Hsuffix &
      %HlookupByte & %Hpointer & %Hlower & %Hupper & Houter)".
  iAssert ((bv_unsigned pointer + 0) ↦ₘ∗
    take 1 (drop (32 * processed) bytes))%I with "[Hprefix]" as "Hprefix0".
  { rewrite Z.add_0_r. iExact "Hprefix". }
  iAssert ((bv_unsigned pointer + 0 + 2) ↦ₘ∗
    drop 2 (drop (32 * processed) bytes))%I with "[Hsuffix]" as "Hsuffix0".
  { rewrite Z.add_0_r. iExact "Hsuffix". }
  iApply "Hbody".
  rewrite /zesu_lbu_byte_array_at_spec.
  iExists pointer, byte, (drop (32 * processed) bytes).
  iFrame "Hsys Htarget Hx19 Hbyte Hprefix0 Hsuffix0".
  repeat iSplit.
  - iPureIntro. reflexivity.
  - iPureIntro. apply lookup_lt_Some in HlookupByte. exact HlookupByte.
  - iPureIntro. exact HlookupByte.
  - iPureIntro. lia.
  - iPureIntro. exact Hupper.
  - rewrite instr_pre'_eq. iNext. iIntros "Hpost".
    iDestruct "Hpost" as
      "(HsysPost & HtargetPost & Hx19Post & HbytePost & HprefixPost &
        HsuffixPost & _)".
    iEval (rewrite Z.add_0_r) in "HprefixPost".
    iEval (cbn; rewrite Z.add_0_r) in "HsuffixPost".
    iApply "Hnext".
    rewrite /writeSuccessBlobHashesLbuResult.
    iFrame "HsysPost Hother HtargetPost Hx19Post HbytePost Hdone HprefixPost
      HsuffixPost Houter".
    repeat iSplit; iPureIntro; assumption.
Qed.
