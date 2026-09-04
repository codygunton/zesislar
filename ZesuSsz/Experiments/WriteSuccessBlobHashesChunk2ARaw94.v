Require Import isla.riscv64.riscv64.
Require Import InstrSpecs.Specs.
From IslaTraces.write_success_blocks Require Import Index.
Require Import IslaTraces.write_success_68.a15494_spec.
Require Import ZesuSsz.Contracts.IslarisCode.
Require Import ZesuSsz.Experiments.WriteSuccessBlobHashesSegment15Frame.

Local Remove Hints a15494_spec_inst : typeclass_instances.

Lemma write_success_blob_hashes_chunk2a_raw_15494
    `{!islaG Sigma} `{!threadG} (P : iProp Sigma)
    (sp pointer : bv 64) (base : Z) (total processed remaining : nat)
    (bytes : list (bv 8)) (tail : spec) (byte : bv 8) :
  instr_lookup_resources IslaTraces.write_success_blocks.Index.lookup -∗
  instr_body 0x15498
    (writeSuccessBlobHashesLbuResult P "x23" 20 2 sp pointer base total
      processed remaining bytes tail byte) -∗
  instr_body 0x15494
    (writeSuccessBlobHashesLbuState P "x23" 20 2 sp pointer base total
      processed remaining bytes tail byte).
Proof.
  iIntros "#Hlookup Hnext".
  iAssert (instr_pre 0x15498
    (writeSuccessBlobHashesLbuResult P "x23" 20 2 sp pointer base total
      processed remaining bytes tail byte))%I with "[Hnext]" as "HnextPre".
  { iApply instr_pre_to_body. iNext. iExact "Hnext". }
  iEval (rewrite /instr_lookup_resources) in "Hlookup".
  iPoseProof ("Hlookup" $! 0x15494 with "[]") as "Hinstr".
  { iPureIntro. rewrite IslaTraces.write_success_blocks.Index.lookup_a15494.
    done. }
  iPoseProof (a15494_spec 0x15494 with "Hinstr") as "Hlbu".
  rewrite instr_pre'_eq. iIntros "Hstate".
  rewrite /writeSuccessBlobHashesLbuState.
  iDestruct "Hstate" as
    "(Hsys & Hother & Htarget & Hx19 & Hbyte & Hdone & Hprefix & Hsuffix &
      %HlookupByte & %Hpointer & %Hlower & %Hupper & Houter)".
  iAssert ((bv_unsigned pointer + 0) ↦ₘ∗
    take 2 (drop (32 * processed) bytes))%I with "[Hprefix]" as "Hprefix0".
  { rewrite Z.add_0_r. iExact "Hprefix". }
  iAssert ((bv_unsigned pointer + 0 + 3) ↦ₘ∗
    drop 3 (drop (32 * processed) bytes))%I with "[Hsuffix]" as "Hsuffix0".
  { rewrite Z.add_0_r. iExact "Hsuffix". }
  iApply "Hlbu".
  rewrite /zesu_lbu_byte_array_at_spec.
  iExists pointer, byte, (drop (32 * processed) bytes).
  iFrame "Hsys Htarget Hx19 Hbyte Hprefix0 Hsuffix0".
  iSplit; first (iPureIntro; lia).
  iSplit; first (iPureIntro;
    apply lookup_lt_Some in HlookupByte; exact HlookupByte).
  iSplit; first (iPureIntro; exact HlookupByte).
  iSplit; first (iPureIntro; split; assumption).
  rewrite instr_pre'_eq. iNext. iIntros "Hpost".
  iDestruct "Hpost" as
    "(HsysPost & HtargetPost & Hx19Post & HbytePost & HprefixPost &
      HsuffixPost & _)".
  iAssert (bv_unsigned pointer ↦ₘ∗
    take 2 (drop (32 * processed) bytes))%I with "[HprefixPost]"
    as "HprefixResult".
  { rewrite Z.add_0_r. iExact "HprefixPost". }
  iAssert ((bv_unsigned pointer + 3) ↦ₘ∗
    drop 3 (drop (32 * processed) bytes))%I with "[HsuffixPost]"
    as "HsuffixResult".
  { rewrite Z.add_0_r. iExact "HsuffixPost". }
  iApply "HnextPre".
  rewrite /writeSuccessBlobHashesLbuResult.
  iFrame "HsysPost Hother HtargetPost Hx19Post HbytePost Hdone HprefixResult
    HsuffixResult Houter".
  repeat iSplit; try iPureIntro; try assumption; done.
Qed.
