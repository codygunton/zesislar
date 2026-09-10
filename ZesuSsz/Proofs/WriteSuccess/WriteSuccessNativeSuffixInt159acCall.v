From Coq Require Import Lists.List ZArith.ZArith.
Require Import isla.riscv64.riscv64.
From IslaTraces.write_success_blocks Require Import Index.
From IslaTraces.write_success_122 Require Import a159ac_spec.
Require Import ZesuSsz.Contracts.IslarisCode.
Require Import ZesuSsz.Contracts.IslarisMachine.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessEncoderIntCall.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessEvents.

Definition writeSuccessSuffixInt159b0CallPost
    `{!islaG Sigma} `{!threadG} (sp : bv 64) (tail : spec) : iProp Sigma :=
  (reg_col zesu_ram_sys_regs ∗
   "x1" ↦ᵣ RVal_Bits (BV 64 0x159b0) ∗ "x2" ↦ᵣ RVal_Bits sp ∗
   "x5" ↦ᵣ RVal_Bits (BV 64 0x2401a0b8) ∗
   "x10" ↦ᵣ RVal_Bits (sp - BV 64 16)%bv ∗
   "x11" ↦ᵣ RVal_Bits (BV 64 8) ∗
   (bv_unsigned sp - 16) ↦ₘ? 16 ∗ mmio_range 0x2401a0c0 16 ∗
   spec_trace tail ∗ True)%I.

Global Instance : LithiumUnfold (@writeSuccessSuffixInt159b0CallPost) := I.

Definition writeSuccessSuffixInt159acCallSpec
    `{!islaG Sigma} `{!threadG} (Q : iProp Sigma) : iProp Sigma :=
  (∃ (sp value : bv 64) (tail : spec),
    reg_col zesu_ram_sys_regs ∗
    "x1" ↦ᵣ RVal_Bits (BV 64 0x159a8) ∗ "x2" ↦ᵣ RVal_Bits sp ∗
    "x5" ↦ᵣ: (fun r => ⌜valu_has_shape r (BitsShape 64)⌝) ∗
    "x10" ↦ᵣ RVal_Bits value ∗
    "x11" ↦ᵣ: (fun r => ⌜valu_has_shape r (BitsShape 64)⌝) ∗
    (bv_unsigned sp - 16) ↦ₘ? 16 ∗ mmio_range 0x2401a0c0 16 ∗
    spec_trace (writeOutputEvents (sp - BV 64 16)%bv (BV 64 8) tail) ∗
    ⌜bv_unsigned sp `mod` 16 = 0⌝ ∗
    ⌜0x20000000 <= bv_unsigned sp - 16⌝ ∗
    ⌜bv_unsigned sp < 0x40000000⌝ ∗
    instr_pre 0x159b0 (writeSuccessSuffixInt159b0CallPost sp tail ∗ Q) ∗ Q)%I.

Global Instance : LithiumUnfold (@writeSuccessSuffixInt159acCallSpec) := I.

Lemma write_success_suffix_int_159ac_call
    `{!islaG Sigma} `{!threadG} (Q : iProp Sigma) :
  instr_lookup_resources IslaTraces.write_success_blocks.Index.lookup -∗
  □ instr_pre 0x15d10 zesuEncoderIntCallSpec -∗
  instr_body 0x159ac (writeSuccessSuffixInt159acCallSpec Q).
Proof.
  iStartProof. iIntros "#Hlookup #Hint".
  iPoseProof "Hlookup" as "#Hlookup159ac".
  iEval (rewrite /instr_lookup_resources) in "Hlookup159ac".
  iPoseProof ("Hlookup159ac" $! 0x159ac with "[]") as "#Hinstr159ac".
  { iPureIntro. rewrite IslaTraces.write_success_blocks.Index.lookup_a159ac.
    done. }
  iPoseProof (IslaTraces.write_success_122.a159ac_spec.a159ac_spec
    0x159ac with "Hinstr159ac") as "Hjalr".
  rewrite instr_pre'_eq. iIntros "Hentry".
  iEval (rewrite /writeSuccessSuffixInt159acCallSpec) in "Hentry".
  iDestruct "Hentry" as (sp value tail)
    "(Hsys & H1 & H2 & H5 & H10 & H11 & Hstack & Hmmio & Htrace &
      %Halign & %Hmin & %Hmax & Hpost & HQ)".
  iApply "Hjalr".
  rewrite /InstrSpecs.Specs.zesu_jalr_same_spec.
  iExists (BV 64 0x159a8). iFrame "Hsys H1".
  iSplit; first (iPureIntro; bv_solve).
  have Htarget :
      bv_unsigned
        (bv_or (bv_and ((BV 64 0x159a8) + BV 64 872)%bv
          (BV 64 18446744073709551614)) (BV 64 0)) = 0x15d10 by
    bv_solve.
  rewrite Htarget.
  iEval (rewrite -instr_pre'_eq) in "Hint".
  iApply (instr_pre_wand 0x15d10 0x15d10 true true with "Hint");
    [done | reflexivity |].
  iIntros "Hcall".
  iEval (unfold zesuEncoderIntCallSpec).
  iExists value, sp, 0x159b0, tail.
  iDestruct "Hcall" as "(HsysCall & H1Call & _)".
  iFrame "HsysCall H1Call H2".
  iEval (rewrite reg_mapsto_pred_eq /reg_mapsto_pred_def) in "H5".
  iEval (rewrite reg_mapsto_pred_eq /reg_mapsto_pred_def).
  iDestruct "H5" as (r5) "(H5 & %Hshape5)".
  iExists r5. iFrame "H5". iSplit; first (iPureIntro; exact Hshape5).
  iFrame "H10".
  iEval (rewrite reg_mapsto_pred_eq /reg_mapsto_pred_def) in "H11".
  iDestruct "H11" as (r11) "(H11 & %Hshape11)".
  iExists r11. iFrame "H11". iSplit; first (iPureIntro; exact Hshape11).
  iFrame "Hstack Hmmio Htrace".
  iSplit; first (iPureIntro; exact Halign).
  iSplit; first (iPureIntro; exact Hmin).
  iSplit; first (iPureIntro; exact Hmax).
  iSplit; first (iPureIntro; lia).
  iSplit; first (iPureIntro; bv_solve).
  iSplit; first (iPureIntro; bv_solve).
  iSplit; first (iPureIntro; bv_solve).
  iSplit; last done.
  rewrite -instr_pre'_eq.
  iApply (instr_pre_wand 0x159b0 0x159b0 true true with "Hpost");
    [done | reflexivity |].
  iIntros "Hreturn".
  iEval (unfold writeSuccessSuffixInt159b0CallPost) in "Hreturn".
  iEval (unfold writeSuccessSuffixInt159b0CallPost).
  have HreturnAddress : Z_to_bv 64 0x159b0 = BV 64 0x159b0 by bv_solve.
  rewrite HreturnAddress. iFrame "Hreturn HQ".
Qed.
