Require Import ZesuSsz.Automation.AllLegacy.
Require Import ZesuMachineMap.Machine.
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Contracts.IslarisMachine.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessEvents.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessHashesLoop.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessLoopCommon.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessSuffixHashes15748Compose.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessSuffixHashesQContinuations.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessSuffixHashesEntryResources.

Definition writeSuccessSuffixHashes15748EntrySource
    `{!islaG Sigma} `{!threadG}
    (P : iProp Sigma)
    (sp pointer : bv 64) (base : Z)
    (total processed remaining : nat) (bytes : list (bv 8))
    (tail : spec) : iProp Sigma :=
  (reg_col zesu_ram_sys_regs ∗
   "x8" ↦ᵣ RVal_Bits (Z_to_bv 64 (Z.of_nat (S remaining))) ∗
   "x10" ↦ᵣ RVal_Bits (Z_to_bv 64 (Z.of_nat (S remaining))) ∗
   (bv_unsigned sp - 16) ↦ₘ? 16 ∗
   mmio_range (machineOutputAddress defaultMap) 16 ∗
   spec_trace
     (writeOutputEventsAny (sp - BV 64 16)%bv (BV 64 8)
       (writeSuccessHashesEvents sp (S remaining) tail)) ∗
   writeSuccessSuffixHashesEntryFrame
     sp pointer base total processed remaining bytes tail P)%I.

Global Instance : LithiumUnfold
    (@writeSuccessSuffixHashes15748EntrySource) := I.

Lemma write_success_suffix_hashes_15748_entry_resource_adapter
    `{!islaG Sigma} `{!threadG}
    (P : iProp Sigma)
    (sp pointer : bv 64) (base : Z)
    (total processed remaining : nat) (bytes : list (bv 8))
    (tail : spec) :
  writeSuccessSuffixHashes15748EntrySource
    P sp pointer base total processed remaining bytes tail -∗
  writeSuccessSuffixHashes15748NonzeroSpec
    sp (Z_to_bv 64 (Z.of_nat (S remaining)))
    (writeSuccessHashesEvents sp (S remaining) tail)
    (writeSuccessSuffixHashesEntryLoopFrame
      sp pointer base total processed remaining bytes tail P).
Proof.
  iIntros "Hsource".
  iEval (rewrite /writeSuccessSuffixHashes15748EntrySource) in "Hsource".
  iDestruct "Hsource" as
    "(Hsys & H8 & H10 & Hstack & Hmmio & Htrace & Hframe)".
  iEval (rewrite /writeSuccessSuffixHashesEntryFrame) in "Hframe".
  iDestruct "Hframe" as
    "(Hregs & H2 & H9 & Hscratch & %Hbounds & Hcaller & _)".
  iEval (rewrite !reg_col_cons reg_col_nil) in "Hregs".
  iDestruct "Hregs" as "(H1 & H5 & H11 & _)".
  destruct Hbounds as (HspAlign & HstackMin & HspTop).
  iAssert ("x1" ↦ᵣ: (fun r => ⌜valu_has_shape r (BitsShape 64)⌝))%I
    with "[H1]" as "H1".
  { rewrite reg_mapsto_pred_eq /reg_mapsto_pred_def.
    iDestruct "H1" as (v Hv) "H1". iExists v. iFrame. done. }
  iAssert ("x5" ↦ᵣ: (fun r => ⌜valu_has_shape r (BitsShape 64)⌝))%I
    with "[H5]" as "H5".
  { rewrite reg_mapsto_pred_eq /reg_mapsto_pred_def.
    iDestruct "H5" as (v Hv) "H5". iExists v. iFrame. done. }
  iAssert ("x11" ↦ᵣ: (fun r => ⌜valu_has_shape r (BitsShape 64)⌝))%I
    with "[H11]" as "H11".
  { rewrite reg_mapsto_pred_eq /reg_mapsto_pred_def.
    iDestruct "H11" as (v Hv) "H11". iExists v. iFrame. done. }
  iAssert (writeSuccessSuffixHashesEntryLoopFrame
      sp pointer base total processed remaining bytes tail P)%I
    with "[H9 Hscratch Hcaller]" as "HloopFrame".
  { rewrite /writeSuccessSuffixHashesEntryLoopFrame. iFrame. }
  iAssert (writeSuccessSuffixHashes15748Q
      sp (Z_to_bv 64 (Z.of_nat (S remaining)))
      (writeSuccessHashesEvents sp (S remaining) tail)
      (writeSuccessSuffixHashesEntryLoopFrame
        sp pointer base total processed remaining bytes tail P))%I
    with "[H8 H2 H5 H10 H11 Hstack Hmmio Htrace HloopFrame]" as "HQ".
  { rewrite /writeSuccessSuffixHashes15748Q.
    iSplitL "H8"; first iExact "H8".
    iSplitL "H2"; first iExact "H2".
    iSplitL "H5"; first iExact "H5".
    iSplitL "H10"; first iExact "H10".
    iSplitL "H11"; first iExact "H11".
    iSplitL "Hstack"; first iExact "Hstack".
    iSplitL "Hmmio"; first iExact "Hmmio".
    iSplitL "Htrace"; first iExact "Htrace".
    iSplit; first by iPureIntro.
    iSplit; first by iPureIntro.
    iSplit; first by iPureIntro.
    iExact "HloopFrame". }
  rewrite /writeSuccessSuffixHashes15748NonzeroSpec.
  iSplitL "Hsys"; first iExact "Hsys".
  iSplitL "H1"; first iExact "H1".
  iSplitL "HQ"; first iExact "HQ".
  done.
Qed.
