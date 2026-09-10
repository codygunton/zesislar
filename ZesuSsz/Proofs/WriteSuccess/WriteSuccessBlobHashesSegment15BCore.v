From Coq Require Import Lists.List ZArith.ZArith.
Require Import isla.riscv64.riscv64.
Require Import InstrSpecs.Specs.
From IslaTraces.write_success_blocks Require Import Index.
Require Import IslaTraces.write_success_67.a15460_spec.
Require Import ZesuSsz.Contracts.IslarisCode.
Require Import ZesuSsz.Experiments.WriteSuccessBlobHashesSpec.
Require Import ZesuSsz.Experiments.WriteSuccessBlobHashesSegment15Frame.

Local Remove Hints a15460_spec_inst : typeclass_instances.

Lemma write_success_blob_hashes_segment15b_core
    `{!islaG Sigma} `{!threadG} (P : iProp Sigma)
    (sp pointer : bv 64) (base : Z) (total processed remaining : nat)
    (bytes : list (bv 8)) (tail : spec) (byte : bv 8) :
  instr_lookup_resources IslaTraces.write_success_blocks.Index.lookup -∗
  instr_body 0x15464
    (writeSuccessBlobHashesLbuResult P "x26" 23 11 sp pointer base total
      processed remaining bytes tail byte) -∗
  instr_body 0x15460 (writeSuccessBlobHashesLbuState P "x26" 23 11 sp
    pointer base total processed remaining bytes tail byte).
Proof.
  iIntros "#Hlookup Hnext".
  iEval (rewrite /instr_lookup_resources) in "Hlookup".
  iPoseProof ("Hlookup" $! 0x15460 with "[]") as "#Hinstr15460".
  { iPureIntro.
    rewrite IslaTraces.write_success_blocks.Index.lookup_a15460.
    done. }
  iPoseProof (IslaTraces.write_success_67.a15460_spec.a15460_spec
    0x15460 with "Hinstr15460") as "Hbody".
  rewrite instr_pre'_eq. iIntros "Hstate".
  rewrite /writeSuccessBlobHashesLbuState.
  iDestruct "Hstate" as
    "(Hsys & Hother & Htarget & Hx19 & Hbyte & Hdone & Hprefix & Hsuffix &
      %HlookupByte & %Hpointer & %Hlower & %Hupper & Houter)".
  iAssert ((bv_unsigned pointer + 0) ↦ₘ∗
    take 11 (drop (32 * processed) bytes))%I
    with "[Hprefix]" as "Hprefix0".
  { rewrite Z.add_0_r. iExact "Hprefix". }
  iAssert ((bv_unsigned pointer + 0 + 12) ↦ₘ∗
    drop 12 (drop (32 * processed) bytes))%I
    with "[Hsuffix]" as "Hsuffix0".
  { rewrite Z.add_0_r. iExact "Hsuffix". }
  iApply "Hbody".
  rewrite /InstrSpecs.Specs.zesu_lbu_byte_array_at_spec.
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
