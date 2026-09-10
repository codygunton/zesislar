From Coq Require Import Lists.List ZArith.ZArith.
Require Import isla.riscv64.riscv64.
From IslaTraces.write_success_blocks Require Import Index.
Require Import ZesuSsz.Contracts.IslarisCode.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessBitvector.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessNativeSuffixConditionalBranch.

Local Remove Hints subsume_instr_pre'_inst : typeclass_instances.
Local Existing Instance subsume_instr_pre_wand_inst | 1.

Definition writeSuccessSuffix15970Frame
    `{!islaG Sigma} `{!threadG} (P : bv 64 -> iProp Sigma)
    (value : bv 64) : iProp Sigma :=
  (∃ sp : bv 64,
    "x2" ↦ᵣ RVal_Bits sp ∗
    (bv_unsigned sp + 72) ↦ₘ value ∗ P value ∗ True)%I.

Global Instance : LithiumUnfold (@writeSuccessSuffix15970Frame) := I.

Lemma write_success_suffix_15970_loaded_branch
    `{!islaG Sigma} `{!threadG} (P : bv 64 -> iProp Sigma) :
  instr_lookup_resources IslaTraces.write_success_blocks.Index.lookup -∗
  instr_body 0x15974 (writeSuccessSuffix15970LoadedSpec P) -∗
  instr_body 0x15994 (writeSuccessSuffix15970LoadedSpec P) -∗
  instr_body 0x15970 (writeSuccessSuffix15970LoadedSpec P).
Proof.
  iStartProof. iIntros "#Hlookup Hnonzero Hzero".
  iPoseProof "Hlookup" as "#Hlookup15970".
  iEval (rewrite /instr_lookup_resources) in "Hlookup15970".
  iPoseProof ("Hlookup15970" $! 0x15970 with "[]") as "#Hinstr15970".
  { iPureIntro. rewrite IslaTraces.write_success_blocks.Index.lookup_a15970.
    done. }
  iPoseProof (write_success_suffix_15970_branch
    (writeSuccessSuffix15970Frame P) with "Hinstr15970") as "Hbranch".
  iAssert (instr_pre 0x15974 (writeSuccessSuffix15970LoadedSpec P))
    with "[Hnonzero]" as "HnonzeroPre".
  { iApply instr_pre_to_body. iNext. rewrite instr_pre'_eq.
    iExact "Hnonzero". }
  iAssert (instr_pre 0x15994 (writeSuccessSuffix15970LoadedSpec P))
    with "[Hzero]" as "HzeroPre".
  { iApply instr_pre_to_body. iNext. rewrite instr_pre'_eq. iExact "Hzero". }
  iApply (instr_pre_wand 0x15970 0x15970 false false with "Hbranch");
    [done | done |].
  iIntros "Hloaded".
  rewrite /writeSuccessSuffix15970LoadedSpec.
  iDestruct "Hloaded" as (sp value) "(Hsys & H2 & H8 & Hvalue & HP)".
  destruct (decide (value = BV 64 0)) as [-> | HvalueNonzero].
  - iLeft.
    rewrite /writeSuccessSuffix15970ZeroSpec /writeSuccessSuffix15970Frame.
    iFrame "Hsys H8".
    iSplitL "H2 Hvalue HP".
    { iExists sp. iFrame. }
    iSplit; last done.
    iApply (instr_pre_wand 0x15994 0x15994 true true with "HzeroPre");
      [done | done |].
    iIntros "Hdestination".
    rewrite /writeSuccessSuffix15970LoadedSpec.
    iDestruct "Hdestination" as "(Hsys & H8 & Hframe)".
    rewrite /writeSuccessSuffix15970Frame.
    iDestruct "Hframe" as (destinationSp) "(H2 & Hvalue & HP & _)".
    iExists destinationSp, (BV 64 0). iFrame.
  - iRight. iExists value. iSplit; first (iPureIntro; exact HvalueNonzero).
    rewrite /writeSuccessSuffix15970NonzeroSpec
      /writeSuccessSuffix15970Frame.
    iFrame "Hsys H8".
    iSplitL "H2 Hvalue HP".
    { iExists sp. iFrame. }
    iSplit; last done.
    iApply (instr_pre_wand 0x15974 0x15974 true true with "HnonzeroPre");
      [done | done |].
    iIntros "Hdestination".
    rewrite /writeSuccessSuffix15970LoadedSpec.
    iDestruct "Hdestination" as "(Hsys & H8 & Hframe)".
    rewrite /writeSuccessSuffix15970Frame.
    iDestruct "Hframe" as (destinationSp) "(H2 & Hvalue & HP & _)".
    iExists destinationSp, value. iFrame.
Qed.

Lemma write_success_suffix_1596c_load_branch
    `{!islaG Sigma} `{!threadG} (P : bv 64 -> iProp Sigma) :
  instr_lookup_resources IslaTraces.write_success_blocks.Index.lookup -∗
  instr_body 0x15974 (writeSuccessSuffix15970LoadedSpec P) -∗
  instr_body 0x15994 (writeSuccessSuffix15970LoadedSpec P) -∗
  instr_body 0x1596c (writeSuccessSuffix1596cLoadSpec P).
Proof.
  iStartProof. iIntros "#Hlookup Hnonzero Hzero".
  iPoseProof (write_success_suffix_15970_loaded_branch P with
    "Hlookup Hnonzero Hzero") as "Hbranch".
  iAssert (instr_pre 0x15970 (writeSuccessSuffix15970LoadedSpec P))
    with "[Hbranch]" as "HbranchPre".
  { iApply instr_pre_to_body. iNext. rewrite instr_pre'_eq.
    iExact "Hbranch". }
  iPoseProof (write_success_suffix_1596c_load P with "Hlookup") as "Hload".
  iApply (instr_pre_wand 0x1596c 0x1596c false false with "Hload");
    [done | done |].
  iIntros "Hentry".
  rewrite /writeSuccessSuffix1596cLoadSpec.
  iDestruct "Hentry" as (sp value)
    "(Hsys & H2 & H8 & Hvalue & %Halign & %Hbounds & HP)".
  destruct Hbounds as (Hlower & Hupper).
  iExists sp, value. iFrame.
  repeat iSplit; iPureIntro; assumption.
Qed.
