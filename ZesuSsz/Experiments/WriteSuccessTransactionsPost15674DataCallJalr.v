From Coq Require Import Lists.List ZArith.ZArith.
Require Import isla.riscv64.riscv64.
From IslaTraces.write_success_blocks Require Import Index.
From IslaTraces.write_success_87 Require Import a15674_spec.
Require Import ZesuSsz.Contracts.IslarisCode.
Require Import ZesuSsz.Contracts.IslarisMachine.
Require Import ZesuSsz.Experiments.WriteSuccessByteLists.
Require Import ZesuSsz.Experiments.WriteSuccessCallAbi.
Require Import ZesuSsz.Experiments.WriteSuccessEvents.
Require Import ZesuSsz.Experiments.WriteSuccessTransactionsPost15674Boundary.
Require Import ZesuSsz.Experiments.WriteSuccessTransactionsPost15674DataCall.
Require Import ZesuSsz.Experiments.WriteSuccessTransactionsLoopExitEvents.
Require Import ZesuSsz.Experiments.WriteSuccessTransactionsPuncturedScratch.

Local Remove Hints subsume_instr_pre'_inst : typeclass_instances.
Local Existing Instance subsume_instr_pre_wand_inst | 1.

(** The data frame keeps the two decoded withdrawal words exact while the
    byte-list encoder owns the lower 80-byte call stack. *)
Definition writeSuccessTransactionsPost15674DataCallEntrySpec
    `{!islaG Sigma} `{!threadG} (P : iProp Sigma) : iProp Sigma :=
  (∃ (sp : bv 64) (base : Z) (total : nat) (tail : spec)
      (first second pointer remaining : bv 64) (items : list ByteListItem)
      (saved : list valu),
    reg_col zesu_ram_sys_regs ∗
    reg_col ((fun r => (KindReg r, BitsShape 64)) <$>
      writeSuccessTransactionsPost15674CallRegisters) ∗
    reg_col (zip_with (fun r v => (KindReg r, ExactShape v))
      writeSuccessTransactionsPost15674Saved saved) ∗
    ⌜length saved = 12%nat⌝ ∗
    ⌜Forall (fun v => valu_has_shape v (BitsShape 64)) saved⌝ ∗
    reg_col ((fun r => (KindReg r, BitsShape 64)) <$>
      writeSuccessTransactionsPost15674ReturnOther) ∗
    "x1" ↦ᵣ RVal_Bits (BV 64 0x15670) ∗
    "x2" ↦ᵣ RVal_Bits sp ∗
    "x10" ↦ᵣ RVal_Bits first ∗
    "x11" ↦ᵣ RVal_Bits second ∗
    writeSuccessTransactionsPuncturedScratch sp base total ∗
    writeSuccessTransactionsLoopCarrierPayload sp first second pointer remaining
      items ∗
    (bv_unsigned sp + 1744) ↦ₘ? 48 ∗
    mmio_range 0x2401a0c0 16 ∗ spec_trace
      (writeOutputEvents (sp - BV 64 48)%bv (BV 64 8)
        (byteListItemEvents (sp - BV 64 32)%bv items tail)) ∗
    P ∗ True)%I.

Global Instance : LithiumUnfold
    (@writeSuccessTransactionsPost15674DataCallEntrySpec) := I.

Definition writeSuccessTransactionsPost15674DataCallReturnSpec
    `{!islaG Sigma} `{!threadG} (P : iProp Sigma) : iProp Sigma :=
  (∃ (sp : bv 64) (base : Z) (total : nat) (tail : spec)
      (first second pointer remaining : bv 64) (items : list ByteListItem)
      (saved : list valu) (r10 r11 : bv 64),
    reg_col zesu_ram_sys_regs ∗
    reg_col ((fun r => (KindReg r, BitsShape 64)) <$>
      writeSuccessTransactionsPost15674Caller) ∗
    reg_col (zip_with (fun r v => (KindReg r, ExactShape v))
      writeSuccessTransactionsPost15674Saved saved) ∗
    ⌜length saved = 12%nat⌝ ∗
    reg_col ((fun r => (KindReg r, BitsShape 64)) <$>
      writeSuccessTransactionsPost15674ReturnOther) ∗
    "x2" ↦ᵣ RVal_Bits sp ∗
    "x10" ↦ᵣ RVal_Bits r10 ∗
    "x11" ↦ᵣ RVal_Bits r11 ∗
    writeSuccessTransactionsPuncturedScratch sp base total ∗
    writeSuccessTransactionsLoopCarrierPayload sp first second pointer remaining
      items ∗
    (bv_unsigned sp + 1744) ↦ₘ? 48 ∗
    mmio_range 0x2401a0c0 16 ∗ spec_trace tail ∗ P ∗ True)%I.

Global Instance : LithiumUnfold
    (@writeSuccessTransactionsPost15674DataCallReturnSpec) := I.

Lemma write_success_transactions_post_15674_data_call_jalr
    `{!islaG Sigma} `{!threadG} (P : iProp Sigma) :
  instr_lookup_resources IslaTraces.write_success_blocks.Index.lookup -∗
  IslaTraces.write_success_blocks.Index.spec_instr_resources -∗
  □ instr_pre 0x15c10 zesuEncoderByteListsCallSpec -∗
  instr_body 0x15678 (writeSuccessTransactionsPost15674DataCallReturnSpec P) -∗
  instr_body 0x15674
    (writeSuccessTransactionsPost15674DataCallEntrySpec P).
Proof.
  iStartProof. iIntros "#Hlookup #Hcode #Hcallee Hnext".
  iPoseProof "Hlookup" as "#Hlookup15674".
  iEval (rewrite /instr_lookup_resources) in "Hlookup15674".
  iPoseProof ("Hlookup15674" $! 0x15674 with "[]") as "#Hinstr15674".
  { iPureIntro.
    rewrite IslaTraces.write_success_blocks.Index.lookup_a15674.
    done. }
  iPoseProof (IslaTraces.write_success_87.a15674_spec.a15674_spec
    0x15674 with "Hinstr15674") as "Hjalr".
  rewrite instr_pre'_eq. iIntros "Hentry".
  iEval (rewrite /writeSuccessTransactionsPost15674DataCallEntrySpec) in "Hentry".
  iDestruct "Hentry" as
    (sp base total tail first second pointer remaining items saved)
    "(Hsys & Hcaller & Hsaved & %HsavedLength & %HsavedShapes & HreturnOther &
      H1 & H2 & H10 & H11 & Hscratch & Hcarrier & Hwithdrawals & Hmmio &
      Htrace & HP & _)".
  iPoseProof (write_success_transactions_post_15674_data_call_frame_enter
    sp base total first second pointer remaining items with
      "Hscratch Hcarrier Hwithdrawals") as "(Hstack80 & Hdata)".
  iEval (rewrite /writeSuccessTransactionsPost15674DataCallFrame) in "Hdata".
  iDestruct "Hdata" as
    "(Hlower104 & HbaseWord & HlengthWord & HscratchPrefix & HscratchFirst &
      HscratchSecond & HscratchPointer & HscratchRemaining & HscratchMiddle &
      HscratchWithdrawals & HscratchTail & Hitems & %Hfacts)".
  destruct Hfacts as
    (HsecondLength & HitemsLength & HfirstAlign & HfirstLower & HfirstUpper &
     HspAlign & HspLower & HspMax).
  have HspMod : bv_unsigned sp `mod` 16 = 0.
  { have HspAlignU := f_equal bv_unsigned HspAlign.
    rewrite bv_extract_0_unsigned in HspAlignU.
    cbn in HspAlignU. bv_solve. }
  iApply "Hjalr".
  rewrite /InstrSpecs.Specs.zesu_jalr_same_spec.
  iExists (BV 64 0x15670). iFrame "Hsys H1".
  iSplit; first (iPureIntro; bv_solve).
  have Htarget :
      bv_unsigned
        (bv_or (bv_and ((BV 64 0x15670) + BV 64 1440)%bv
          (BV 64 18446744073709551614)) (BV 64 0)) = 0x15c10
    by native_compute.
  rewrite Htarget.
  iEval (rewrite -instr_pre'_eq) in "Hcallee".
  iApply (instr_pre_wand 0x15c10 0x15c10 true true with "Hcallee");
    [done | reflexivity |].
  iIntros "(HjalrSys & Hjalr1 & _)".
  have Hret : Z_to_bv 64 (0x15674 + 4) = BV 64 0x15678 by bv_solve.
  iEval (rewrite Hret) in "Hjalr1".
  iEval (unfold zesuEncoderByteListsCallSpec, zesu_c_call).
  iExists sp, (BV 64 0x15678).
  iEval (unfold writeSuccessTransactionsPost15674CallRegisters; cbn) in "Hcaller".
  iDestruct "Hcaller" as
    "(H12 & H13 & H14 & H15 & H16 & H17 & H5 & H6 & H7 & H28 & H29 & H30 & H31 & _)".
  destruct saved as [|v8 saved]; cbn in HsavedLength; try lia.
  destruct saved as [|v9 saved]; cbn in HsavedLength; try lia.
  destruct saved as [|v18 saved]; cbn in HsavedLength; try lia.
  destruct saved as [|v19 saved]; cbn in HsavedLength; try lia.
  destruct saved as [|v20 saved]; cbn in HsavedLength; try lia.
  destruct saved as [|v21 saved]; cbn in HsavedLength; try lia.
  destruct saved as [|v22 saved]; cbn in HsavedLength; try lia.
  destruct saved as [|v23 saved]; cbn in HsavedLength; try lia.
  destruct saved as [|v24 saved]; cbn in HsavedLength; try lia.
  destruct saved as [|v25 saved]; cbn in HsavedLength; try lia.
  destruct saved as [|v26 saved]; cbn in HsavedLength; try lia.
  destruct saved as [|v27 saved]; cbn in HsavedLength; try lia.
  destruct saved as [|vrest rest]; cbn in HsavedLength; try lia.
  repeat rewrite Forall_cons_iff in HsavedShapes.
  destruct HsavedShapes as
    (Hv8 & Hv9 & Hv18 & Hv19 & Hv20 & Hv21 & Hv22 & Hv23 & Hv24 & Hv25 &
     Hv26 & Hv27 & _).
  iEval (unfold writeSuccessTransactionsPost15674Saved; cbn) in "Hsaved".
  iDestruct "Hsaved" as
    "(H8 & H9 & H18 & H19 & H20 & H21 & H22 & H23 & H24 & H25 & H26 & H27 & _)".
  iDestruct "H12" as (r12) "(%Hr12 & H12)".
  apply (proj2 (simpl_impl (P := valu_has_shape r12 (BitsShape 64))
    (Ps := ∃ b12 : bv 64, r12 = RVal_Bits b12))) in Hr12.
  destruct Hr12 as (b12 & ->).
  iDestruct "H13" as (r13) "(%Hr13 & H13)".
  apply (proj2 (simpl_impl (P := valu_has_shape r13 (BitsShape 64))
    (Ps := ∃ b13 : bv 64, r13 = RVal_Bits b13))) in Hr13.
  destruct Hr13 as (b13 & ->).
  iDestruct "H14" as (r14) "(%Hr14 & H14)".
  apply (proj2 (simpl_impl (P := valu_has_shape r14 (BitsShape 64))
    (Ps := ∃ b14 : bv 64, r14 = RVal_Bits b14))) in Hr14.
  destruct Hr14 as (b14 & ->).
  iDestruct "H15" as (r15) "(%Hr15 & H15)".
  apply (proj2 (simpl_impl (P := valu_has_shape r15 (BitsShape 64))
    (Ps := ∃ b15 : bv 64, r15 = RVal_Bits b15))) in Hr15.
  destruct Hr15 as (b15 & ->).
  iDestruct "H16" as (r16) "(%Hr16 & H16)".
  apply (proj2 (simpl_impl (P := valu_has_shape r16 (BitsShape 64))
    (Ps := ∃ b16 : bv 64, r16 = RVal_Bits b16))) in Hr16.
  destruct Hr16 as (b16 & ->).
  iDestruct "H17" as (r17) "(%Hr17 & H17)".
  apply (proj2 (simpl_impl (P := valu_has_shape r17 (BitsShape 64))
    (Ps := ∃ b17 : bv 64, r17 = RVal_Bits b17))) in Hr17.
  destruct Hr17 as (b17 & ->).
  iDestruct "H8" as (r8) "(%Hr8 & H8)".
  iAssert ("x8" ↦ᵣ: fun r => ⌜valu_has_shape r (BitsShape 64)⌝)%I
    with "[H8]" as "H8bits".
  { rewrite reg_mapsto_pred_eq /reg_mapsto_pred_def.
    iExists r8. iFrame. iPureIntro. rewrite Hr8. exact Hv8. }
  iDestruct "H9" as (r9) "(%Hr9 & H9)".
  iAssert ("x9" ↦ᵣ: fun r => ⌜valu_has_shape r (BitsShape 64)⌝)%I
    with "[H9]" as "H9bits".
  { rewrite reg_mapsto_pred_eq /reg_mapsto_pred_def.
    iExists r9. iFrame. iPureIntro. rewrite Hr9. exact Hv9. }
  iDestruct "H18" as (r18) "(%Hr18 & H18)".
  iAssert ("x18" ↦ᵣ: fun r => ⌜valu_has_shape r (BitsShape 64)⌝)%I
    with "[H18]" as "H18bits".
  { rewrite reg_mapsto_pred_eq /reg_mapsto_pred_def.
    iExists r18. iFrame. iPureIntro. rewrite Hr18. exact Hv18. }
  iDestruct "H19" as (r19) "(%Hr19 & H19)".
  iAssert ("x19" ↦ᵣ: fun r => ⌜valu_has_shape r (BitsShape 64)⌝)%I
    with "[H19]" as "H19bits".
  { rewrite reg_mapsto_pred_eq /reg_mapsto_pred_def.
    iExists r19. iFrame. iPureIntro. rewrite Hr19. exact Hv19. }
  iDestruct "H20" as (r20) "(%Hr20 & H20)".
  iAssert ("x20" ↦ᵣ: fun r => ⌜valu_has_shape r (BitsShape 64)⌝)%I
    with "[H20]" as "H20bits".
  { rewrite reg_mapsto_pred_eq /reg_mapsto_pred_def.
    iExists r20. iFrame. iPureIntro. rewrite Hr20. exact Hv20. }
  iDestruct "H21" as (r21) "(%Hr21 & H21)".
  iAssert ("x21" ↦ᵣ: fun r => ⌜valu_has_shape r (BitsShape 64)⌝)%I
    with "[H21]" as "H21bits".
  { rewrite reg_mapsto_pred_eq /reg_mapsto_pred_def.
    iExists r21. iFrame. iPureIntro. rewrite Hr21. exact Hv21. }
  iDestruct "H22" as (r22) "(%Hr22 & H22)".
  iAssert ("x22" ↦ᵣ: fun r => ⌜valu_has_shape r (BitsShape 64)⌝)%I
    with "[H22]" as "H22bits".
  { rewrite reg_mapsto_pred_eq /reg_mapsto_pred_def.
    iExists r22. iFrame. iPureIntro. rewrite Hr22. exact Hv22. }
  iDestruct "H23" as (r23) "(%Hr23 & H23)".
  iAssert ("x23" ↦ᵣ: fun r => ⌜valu_has_shape r (BitsShape 64)⌝)%I
    with "[H23]" as "H23bits".
  { rewrite reg_mapsto_pred_eq /reg_mapsto_pred_def.
    iExists r23. iFrame. iPureIntro. rewrite Hr23. exact Hv23. }
  iDestruct "H24" as (r24) "(%Hr24 & H24)".
  iAssert ("x24" ↦ᵣ: fun r => ⌜valu_has_shape r (BitsShape 64)⌝)%I
    with "[H24]" as "H24bits".
  { rewrite reg_mapsto_pred_eq /reg_mapsto_pred_def.
    iExists r24. iFrame. iPureIntro. rewrite Hr24. exact Hv24. }
  iDestruct "H25" as (r25) "(%Hr25 & H25)".
  iAssert ("x25" ↦ᵣ: fun r => ⌜valu_has_shape r (BitsShape 64)⌝)%I
    with "[H25]" as "H25bits".
  { rewrite reg_mapsto_pred_eq /reg_mapsto_pred_def.
    iExists r25. iFrame. iPureIntro. rewrite Hr25. exact Hv25. }
  iDestruct "H26" as (r26) "(%Hr26 & H26)".
  iAssert ("x26" ↦ᵣ: fun r => ⌜valu_has_shape r (BitsShape 64)⌝)%I
    with "[H26]" as "H26bits".
  { rewrite reg_mapsto_pred_eq /reg_mapsto_pred_def.
    iExists r26. iFrame. iPureIntro. rewrite Hr26. exact Hv26. }
  iDestruct "H27" as (r27) "(%Hr27 & H27)".
  iAssert ("x27" ↦ᵣ: fun r => ⌜valu_has_shape r (BitsShape 64)⌝)%I
    with "[H27]" as "H27bits".
  { rewrite reg_mapsto_pred_eq /reg_mapsto_pred_def.
    iExists r27. iFrame. iPureIntro. rewrite Hr27. exact Hv27. }
  iAssert ("x1" ↦ᵣ RVal_Bits (BV 64 0x15678))%I with "[Hjalr1]" as "Hret1".
  { iExact "Hjalr1". }
  iAssert (reg_col ((fun r => (KindReg r, BitsShape 64)) <$> tmp_registers))%I
    with "[H5 H6 H7 H28 H29 H30 H31]" as "Htmp".
  { cbn. iFrame. }
  iEval (rewrite reg_mapsto_pred_eq /reg_mapsto_pred_def)
    in "H8bits H9bits H18bits H19bits H20bits H21bits H22bits H23bits H24bits
      H25bits H26bits H27bits".
  iDestruct "H8bits" as (a8) "(H8 & %Ha8)".
  iDestruct "H9bits" as (a9) "(H9 & %Ha9)".
  iDestruct "H18bits" as (a18) "(H18 & %Ha18)".
  iDestruct "H19bits" as (a19) "(H19 & %Ha19)".
  iDestruct "H20bits" as (a20) "(H20 & %Ha20)".
  iDestruct "H21bits" as (a21) "(H21 & %Ha21)".
  iDestruct "H22bits" as (a22) "(H22 & %Ha22)".
  iDestruct "H23bits" as (a23) "(H23 & %Ha23)".
  iDestruct "H24bits" as (a24) "(H24 & %Ha24)".
  iDestruct "H25bits" as (a25) "(H25 & %Ha25)".
  iDestruct "H26bits" as (a26) "(H26 & %Ha26)".
  iDestruct "H27bits" as (a27) "(H27 & %Ha27)".
  liARun.
  Unshelve. all: prepare_sidecond.
  all: try assumption.
  all: try iFrame.
  all: try bv_solve.
  all: try lia.
  all: try exact HspMod.
  Unshelve.
  iExists (tail, items, tt)ₗ.
  iFrame "Hitems Hmmio Htrace".
  repeat iSplit; try iPureIntro; try assumption; try lia.
  iApply instr_pre_to_body. iNext.
  iEval (rewrite -instr_pre'_eq) in "Hnext".
  iApply (instr_pre_wand 0x15678 0x15678 false false with "Hnext");
    [done | done |].
  iIntros "Hpost".
  iEval (unfold zesu_c_call_ret) in "Hpost".
  iDestruct "Hpost" as "(HpostSys & HpostCaller & HpostSaved & HpostRest)".
  iEval (rewrite reg_mapsto_pred_eq /reg_mapsto_pred_def) in "HpostRest".
  iDestruct "HpostRest" as (r10) "(Hpost10 & HpostRest)".
  iDestruct "HpostRest" as (b10) "(%Hr10 & HpostRest)". subst r10.
  iDestruct "HpostRest" as (r11) "(Hpost11 & HpostRest)".
  iDestruct "HpostRest" as (b11) "(%Hr11 & HpostRest)". subst r11.
  iDestruct "HpostRest" as
    "(Hpost2 & HpostStack & HpostItems & HpostMmio & HpostTrace & _)".
  iAssert (writeSuccessTransactionsPost15674DataCallFrame sp base total
    first second pointer remaining items)%I
    with "[Hlower104 HbaseWord HlengthWord HscratchPrefix HscratchFirst
      HscratchSecond HscratchPointer HscratchRemaining HscratchMiddle
      HscratchWithdrawals HscratchTail HpostItems]" as "Hdata".
  { iEval (rewrite /writeSuccessTransactionsPost15674DataCallFrame).
    iFrame. iPureIntro. repeat split; assumption. }
  iPoseProof (write_success_transactions_post_15674_data_call_frame_exit
    sp base total first second pointer remaining items with
      "HpostStack Hdata") as "(Hscratch & Hcarrier & Hwithdrawals)".
  iEval (rewrite /writeSuccessTransactionsPost15674DataCallReturnSpec).
  iExists sp, base, total, tail, first, second, pointer, remaining, items,
    [a8; a9; a18; a19; a20; a21; a22; a23; a24; a25; a26; a27], b10, b11.
  iFrame "HpostSys HpostCaller HpostSaved HreturnOther Hpost2 Hpost10 Hpost11
    Hscratch Hcarrier Hwithdrawals HpostMmio HpostTrace HP".
  iPureIntro. reflexivity.
Qed.
