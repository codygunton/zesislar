Require Import ZesuSsz.Automation.AllLegacy.
Require Import ZesuMachineMap.Machine.
From Coq Require Import Lists.List ZArith.ZArith.
Require Import isla.riscv64.riscv64.
From IslaTraces.write_success_blocks Require Import Index.
From IslaTraces.write_success_119 Require Import a1598c_spec.
Require Import ZesuSsz.Contracts.IslarisCode.
Require Import ZesuSsz.Contracts.IslarisMachine.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessEncoderBytesCall.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessEvents.

Definition writeSuccessSuffixBytes15990CallPost
    `{!islaG Sigma} `{!threadG}
    (sp data size oldS0 oldS1 : bv 64) (bytes : list (bv 8))
    (tail : spec) : iProp Sigma :=
  (reg_col zesu_ram_sys_regs ∗
   "x1" ↦ᵣ RVal_Bits (BV 64 0x15990) ∗ "x2" ↦ᵣ RVal_Bits sp ∗
   "x5" ↦ᵣ RVal_Bits (BV 64 (mapIoContextAddress defaultMap)) ∗
   "x6" ↦ᵣ: (fun r => ⌜valu_has_shape r (BitsShape 64)⌝) ∗
   "x8" ↦ᵣ RVal_Bits oldS0 ∗ "x9" ↦ᵣ RVal_Bits oldS1 ∗
   "x10" ↦ᵣ RVal_Bits data ∗ "x11" ↦ᵣ RVal_Bits size ∗
   (bv_unsigned sp - 48) ↦ₘ? 48 ∗ bv_unsigned data ↦ₘ∗ bytes ∗
   mmio_range (machineOutputAddress defaultMap) 16 ∗ spec_trace tail ∗ True)%I.

Global Instance : LithiumUnfold (@writeSuccessSuffixBytes15990CallPost) := I.

Definition writeSuccessSuffixBytes1598cCallSpec
    `{!islaG Sigma} `{!threadG} (Q : iProp Sigma) : iProp Sigma :=
  (∃ (sp data size oldS0 oldS1 : bv 64) (bytes : list (bv 8))
      (tail : spec),
    reg_col zesu_ram_sys_regs ∗
    "x1" ↦ᵣ RVal_Bits (BV 64 0x15988) ∗ "x2" ↦ᵣ RVal_Bits sp ∗
    "x5" ↦ᵣ: (fun r => ⌜valu_has_shape r (BitsShape 64)⌝) ∗
    "x6" ↦ᵣ: (fun r => ⌜valu_has_shape r (BitsShape 64)⌝) ∗
    "x8" ↦ᵣ RVal_Bits oldS0 ∗ "x9" ↦ᵣ RVal_Bits oldS1 ∗
    "x10" ↦ᵣ RVal_Bits data ∗ "x11" ↦ᵣ RVal_Bits size ∗
    (bv_unsigned sp - 48) ↦ₘ? 48 ∗ bv_unsigned data ↦ₘ∗ bytes ∗
    ⌜bv_unsigned size = length bytes⌝ ∗
    mmio_range (machineOutputAddress defaultMap) 16 ∗
    spec_trace
      (writeOutputEventsAny (sp - BV 64 48)%bv (BV 64 8)
        (writeOutputEventsAny data size tail)) ∗
    ⌜bv_unsigned sp `mod` 16 = 0⌝ ∗
    ⌜(mapRamBase defaultMap) <= bv_unsigned sp - 48⌝ ∗
    ⌜bv_unsigned sp < (machineRamEnd defaultMap)⌝ ∗
    instr_pre 0x15990
      (writeSuccessSuffixBytes15990CallPost
        sp data size oldS0 oldS1 bytes tail ∗ Q) ∗
    Q)%I.

Global Instance : LithiumUnfold (@writeSuccessSuffixBytes1598cCallSpec) := I.

Lemma write_success_suffix_bytes_1598c_call
    `{!islaG Sigma} `{!threadG} (Q : iProp Sigma) :
  instr_lookup_resources IslaTraces.write_success_blocks.Index.lookup -∗
  □ instr_pre 0x15c6c zesuEncoderBytesCallSpec -∗
  instr_body 0x1598c (writeSuccessSuffixBytes1598cCallSpec Q).
Proof.
  iStartProof. iIntros "#Hlookup #Hbytes".
  iPoseProof "Hlookup" as "#Hlookup1598c".
  iEval (rewrite /instr_lookup_resources) in "Hlookup1598c".
  iPoseProof ("Hlookup1598c" $! 0x1598c with "[]") as "#Hinstr1598c".
  { iPureIntro. rewrite IslaTraces.write_success_blocks.Index.lookup_a1598c.
    done. }
  iPoseProof (IslaTraces.write_success_119.a1598c_spec.a1598c_spec
    0x1598c with "Hinstr1598c") as "Hjalr".
  rewrite instr_pre'_eq. iIntros "Hentry".
  iEval (rewrite /writeSuccessSuffixBytes1598cCallSpec) in "Hentry".
  iDestruct "Hentry" as
    (sp data size oldS0 oldS1 bytes tail)
    "(Hsys & H1 & H2 & H5 & H6 & H8 & H9 & H10 & H11 & Hstack &
      Hdata & %Hlen & Hmmio & Htrace & %Halign & %Hmin & %Hmax &
      Hpost & HQ)".
  iApply "Hjalr".
  rewrite /InstrSpecs.Specs.zesu_jalr_same_spec.
  iExists (BV 64 0x15988). iFrame "Hsys H1".
  iSplit; first (iPureIntro; bv_solve).
  have Htarget :
      bv_unsigned
        (bv_or (bv_and ((BV 64 0x15988) + BV 64 740)%bv
          (BV 64 18446744073709551614)) (BV 64 0)) = 0x15c6c by
    bv_solve.
  rewrite Htarget.
  iEval (rewrite -instr_pre'_eq) in "Hbytes".
  iApply (instr_pre_wand 0x15c6c 0x15c6c true true with "Hbytes");
    [done | reflexivity |].
  iIntros "Hcall".
  iEval (unfold zesuEncoderBytesCallSpec).
  iExists data, size, sp, oldS0, oldS1, 0x15990, bytes, tail.
  iDestruct "Hcall" as "(HsysCall & H1Call & _)".
  iFrame "HsysCall H1Call H2".
  iEval (rewrite reg_mapsto_pred_eq /reg_mapsto_pred_def) in "H5".
  iEval (rewrite reg_mapsto_pred_eq /reg_mapsto_pred_def).
  iDestruct "H5" as (r5) "(H5 & %Hshape5)".
  iExists r5. iFrame "H5". iSplit; first (iPureIntro; exact Hshape5).
  iEval (rewrite reg_mapsto_pred_eq /reg_mapsto_pred_def) in "H6".
  iDestruct "H6" as (r6) "(H6 & %Hshape6)".
  iExists r6. iFrame "H6". iSplit; first (iPureIntro; exact Hshape6).
  iFrame "H8 H9 H10 H11 Hstack Hdata Hmmio Htrace".
  repeat iSplit; try iPureIntro; try assumption; try bv_solve; try lia.
  rewrite -instr_pre'_eq.
  iApply (instr_pre_wand 0x15990 0x15990 true true with "Hpost");
    [done | reflexivity |].
  iIntros "Hreturn".
  iDestruct "Hreturn" as "(Hreturn & HQreturn)".
  iDestruct "HQreturn" as
    "(H1r & H2r & H5r & H6r & H8r & H9r & H10r & H11r & Hstackr &
      Hdatar & Hmmior & Htracer & _)".
  iEval (unfold writeSuccessSuffixBytes15990CallPost) in "Hreturn".
  iEval (unfold writeSuccessSuffixBytes15990CallPost).
  have HreturnAddress : Z_to_bv 64 0x15990 = BV 64 0x15990 by bv_solve.
  rewrite HreturnAddress.
  iEval (rewrite reg_mapsto_pred_eq /reg_mapsto_pred_def).
  iFrame "Hreturn H1r H2r H5r H6r H8r H9r H10r H11r Hstackr Hdatar
    Hmmior Htracer HQ".
Qed.
