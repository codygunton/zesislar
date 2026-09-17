Require Import ZesuSsz.Automation.All.
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Export.Snapshots.
Require Import ZesuSsz.Proofs.WriteSuccess.Interfaces.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessExactSuffixHashesLoopSpec.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessExactSuffixBytesPayloadSpec.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessEvents.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessOutputSemantic.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessObservation.

Import ListNotations.
Open Scope Z_scope.

Definition suffixTailFieldsCaller `{!islaG Sigma} `{!threadG}
    (sp data size : bv 64) (bytes : list (bv 8)) (P : iProp Sigma) :
    iProp Sigma :=
  ("x6" ↦ᵣ: (fun value => ⌜valu_has_shape value (BitsShape 64)⌝) ∗
   reg_col ((fun register => (KindReg register, BitsShape 64)) <$>
     ["x3"; "x4"; "x7"; "x17"; "x18"; "x19"; "x20"; "x21";
      "x22"; "x23"; "x24"; "x25"; "x26"; "x27"; "x28"; "x29";
      "x30"; "x31"]) ∗
   (bv_unsigned sp - 48) ↦ₘ? 48 ∗
   (bv_unsigned sp + 920) ↦ₘ data ∗
   (bv_unsigned sp + 928) ↦ₘ size ∗
   bv_unsigned data ↦ₘ∗ bytes ∗
   ⌜bv_unsigned size = length bytes⌝ ∗
   ⌜bv_unsigned sp `mod` 16 = 0⌝ ∗
   ⌜mapRamBase defaultMap <= bv_unsigned sp - 48⌝ ∗
   ⌜bv_unsigned sp < machineRamEnd defaultMap⌝ ∗
   ⌜bv_unsigned sp + 1896 < machineRamEnd defaultMap⌝ ∗
   P ∗ True)%I.
Global Instance : LithiumUnfold (@suffixTailFieldsCaller) := I.

Lemma write_success_exact_suffix_hashes_tail_connection
    `{!islaG Sigma} `{!threadG}
    (sp data size : bv 64) (hashBase : Z)
    (hashBytes bytes : list (bv 8)) (tail : spec) (P : iProp Sigma) :
  instr_body 0x158e0
    (writeSuccessExactTailFieldsEntryBoundary sp data size (BV 64 0)
      (Z_to_bv 64 (hashBase + Z.of_nat (length hashBytes)))
      bytes tail (hashBase ↦ₘ∗ hashBytes ∗ suffixLoopScratch sp ∗ P)) -∗
  instr_body 0x158e0
    (suffixLoopExit sp hashBase hashBytes
      (writeOutputEvents (sp - BV 64 48)%bv (BV 64 8)
        (writeSuccessPrivateBytes (writeSuccessEncodeU64 (bv_unsigned size)))
        (writeOutputEvents data size bytes tail))
      (suffixTailFieldsCaller sp data size bytes P)).
Proof.
  iStartProof. iIntros "Htail".
  iApply (instr_pre_wand 0x158e0 0x158e0 false false with "Htail");
    [done | reflexivity |].
  iIntros "Hentry".
  rewrite /suffixLoopExit /suffixTailFieldsCaller
    /writeSuccessExactTailFieldsEntryBoundary
    /exactSuffixBytesPayloadEntryAt /exactSuffixBytesPayloadFrame.
  iDestruct "Hentry" as
    "(Hsys & H2 & H1 & H5 & H8 & H9 & Hregs & Hhash & Hscratch &
      Hmmio & Htrace & Hcaller & _)".
  iDestruct "Hcaller" as
    "(H6 & Hother & Hstack & HdataSlot & HsizeSlot & Hdata & %Hlength &
      %Halign & %Hlow & %Hhigh & %Htop & HP & _)".
  iAssert ("x1" ↦ᵣ: (fun value =>
      ⌜valu_has_shape value (BitsShape 64)⌝))%I with "[H1]" as "H1".
  { rewrite reg_mapsto_pred_eq /reg_mapsto_pred_def. iExists _. iFrame. done. }
  iAssert ("x5" ↦ᵣ: (fun value =>
      ⌜valu_has_shape value (BitsShape 64)⌝))%I with "[H5]" as "H5".
  { rewrite reg_mapsto_pred_eq /reg_mapsto_pred_def. iExists _. iFrame. done. }
  iEval (rewrite !reg_col_cons reg_col_nil) in "Hregs".
  iDestruct "Hregs" as
    "(H10 & H11 & H12 & H13 & H14 & H15 & H16 & _)".
  iEval (rewrite !reg_col_cons reg_col_nil) in "Hother".
  iDestruct "Hother" as
    "(H3 & H4 & H7 & H17 & H18 & H19 & H20 & H21 & H22 & H23 & H24 &
      H25 & H26 & H27 & H28 & H29 & H30 & H31 & _)".
  iAssert (reg_col ((fun register => (KindReg register, BitsShape 64)) <$>
      WriteSuccessExactSuffixBytesPayload158e0.exactSuffixBytesOtherRegisters))%I
    with "[H3 H4 H7 H12 H13 H14 H15 H16 H17 H18 H19 H20 H21 H22 H23
      H24 H25 H26 H27 H28 H29 H30 H31]" as "HfinalRegs".
  { rewrite /WriteSuccessExactSuffixBytesPayload158e0.exactSuffixBytesOtherRegisters.
    iEval (rewrite !reg_col_cons reg_col_nil). iFrame. }
  iFrame "Hsys H1 H2 H5 H6 H8 H9 Hstack Hmmio Htrace Hdata
    HdataSlot HsizeSlot Hhash Hscratch HP HfinalRegs".
  rewrite !reg_mapsto_pred_eq /reg_mapsto_pred_def.
  iDestruct "H10" as (v10) "(%Hv10 & H10)".
  iDestruct "H11" as (v11) "(%Hv11 & H11)".
  iSplitL "H10"; first (iExists v10; iFrame; done).
  iSplitL "H11"; first (iExists v11; iFrame; done).
  repeat iSplit; try iPureIntro; try assumption; try done.
Qed.

Print Assumptions write_success_exact_suffix_hashes_tail_connection.
