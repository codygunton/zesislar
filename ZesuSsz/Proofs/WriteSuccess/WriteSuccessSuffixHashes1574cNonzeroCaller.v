Require Import ZesuSsz.Automation.All.
Require Import ZesuMachineMap.Machine.
Require Import isla.riscv64.riscv64.
Require Import InstrSpecs.Machine.
Require Import IslaTraces.write_success_101.a1574c_spec.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessEncoderIntCall.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessSuffixHashes1574cCall.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessSuffixHashes15750Branch.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessSuffixHashesCallContinuations.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessSuffixHashesBranchAdapters.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessEvents.

Definition writeSuccessSuffixHashes1574cNonzeroSpec
    `{!islaG Sigma} `{!threadG}
    (sp value : bv 64) (tail : spec) (Q : iProp Sigma) : iProp Sigma :=
  (reg_col zesu_ram_sys_regs ∗
   "x1" ↦ᵣ RVal_Bits (BV 64 0x15748) ∗
   "x2" ↦ᵣ RVal_Bits sp ∗
   "x5" ↦ᵣ: (fun r5 => ⌜valu_has_shape r5 (BitsShape 64)⌝) ∗
   "x8" ↦ᵣ RVal_Bits value ∗
   "x10" ↦ᵣ RVal_Bits value ∗
   "x11" ↦ᵣ: (fun r11 => ⌜valu_has_shape r11 (BitsShape 64)⌝) ∗
   (bv_unsigned sp - 16) ↦ₘ? 16 ∗
   mmio_range (machineOutputAddress defaultMap) 16 ∗
   spec_trace (writeOutputEventsAny (sp - BV 64 16)%bv (BV 64 8) tail) ∗
   ⌜bv_unsigned sp `mod` 16 = 0⌝ ∗
   ⌜(mapRamBase defaultMap) <= bv_unsigned sp - 16⌝ ∗
   ⌜bv_unsigned sp < (machineRamEnd defaultMap)⌝ ∗
   Q)%I.

Global Instance : LithiumUnfold
  (@writeSuccessSuffixHashes1574cNonzeroSpec) := I.

Lemma write_success_suffix_hashes_1574c_nonzero_caller
    `{!islaG Sigma} `{!threadG}
    (sp value : bv 64) (tail : spec) (Q : iProp Sigma)
    (Hvalue : value <> BV 64 0) :
  instr 0x1574c (Some IslaTraces.write_success_101.a1574c.a1574c) -∗
  □ instr_pre 0x15d10 zesuEncoderIntCallSpec -∗
  instr_body 0x15750
    (writeSuccessSuffixHashes15750NonzeroState value
      (writeSuccessSuffixHashes15750NonzeroQ sp value tail Q)) -∗
  instr_body 0x1574c
    (writeSuccessSuffixHashes1574cNonzeroSpec sp value tail Q).
Proof.
  iStartProof. iIntros "Hinstr #Hint Hbranch".
  iPoseProof (IslaTraces.write_success_101.a1574c_spec.a1574c_spec
    0x1574c with "Hinstr") as "Hjalr".
  rewrite instr_pre'_eq. iIntros "Hentry".
  iEval (rewrite /writeSuccessSuffixHashes1574cNonzeroSpec) in "Hentry".
  iDestruct "Hentry" as
    "(Hsys & H1 & H2 & H5 & H8 & H10 & H11 & Hstack & Hmmio & Htrace &
      %Halign & %Hmin & %Hmax & HQ)".
  iApply "Hjalr".
  rewrite /InstrSpecs.Specs.zesu_jalr_same_spec.
  iExists (BV 64 0x15748).
  iFrame "Hsys H1".
  iSplit; first (iPureIntro; bv_solve).
  have Htarget :
      bv_unsigned
        (bv_or (bv_and ((BV 64 0x15748) + BV 64 1480)%bv
          (BV 64 18446744073709551614)) (BV 64 0)) = 0x15d10 by
    native_compute.
  rewrite Htarget.
  iEval (rewrite -instr_pre'_eq) in "Hint".
  iApply (instr_pre_wand 0x15d10 0x15d10 true true with "Hint");
    [done | reflexivity |].
  iIntros "Hcall".
  iEval (unfold zesuEncoderIntCallSpec).
  iExists value, sp, 0x15750, tail.
  iDestruct "Hcall" as "(HsysCall & H1Call & _)".
  iFrame "HsysCall H1Call".
  iEval (rewrite reg_mapsto_pred_eq /reg_mapsto_pred_def) in "H5".
  iEval (rewrite reg_mapsto_pred_eq /reg_mapsto_pred_def).
  iFrame "H2".
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
  iEval (rewrite -instr_pre'_eq) in "Hbranch".
  iAssert (writeSuccessSuffixHashes1574cCallPost sp value tail -∗
    writeSuccessSuffixHashes15750NonzeroState value
      (writeSuccessSuffixHashes15750NonzeroQ sp value tail Q))%I
    with "[H8 HQ]" as "Hwand".
  { iIntros "HpostState".
    iEval (unfold writeSuccessSuffixHashes1574cCallPost) in "HpostState".
    rewrite /writeSuccessSuffixHashes15750NonzeroState.
    rewrite /writeSuccessSuffixHashes15750NonzeroQ.
    have H15750 : Z_to_bv 64 0x15750 = BV 64 0x15750 by bv_solve.
    rewrite <- H15750.
    iDestruct "HpostState" as
      "(HsysPost & Hx1Post & Hx2Post & Hx5Post & Hx10Post & Hx11Post &
        HstackPost & HmmioPost & HtracePost & _)".
    iFrame. }
  iPoseProof (write_success_suffix_hashes_15750_nonzero_pre_adapter
      value (writeSuccessSuffixHashes15750NonzeroQ sp value tail Q)
      (writeSuccessSuffixHashes1574cCallPost sp value tail) Hvalue
      with "Hwand Hbranch") as "HbranchPre".
  iEval (unfold writeSuccessSuffixHashes1574cCallPost) in "HbranchPre".
  iFrame "HbranchPre".
Qed.
