From Coq Require Import Lists.List ZArith.ZArith.
Require Import isla.riscv64.riscv64.
From IslaTraces.write_success_blocks Require Import Index.
From IslaTraces.write_success_121 Require Import a1599c_spec.
Require Import ZesuSsz.Contracts.IslarisCode.
Require Import ZesuSsz.Contracts.IslarisMachine.
Require Import ZesuSsz.Experiments.WriteSuccessCallAbi.
Require Import ZesuSsz.Experiments.WriteSuccessEncoderBooleanCall.
Require Import ZesuSsz.Experiments.WriteSuccessEvents.

Definition writeSuccessSuffixBooleanSavedRegisters : list string :=
  ["x8"; "x9"; "x18"; "x19"; "x20"; "x21";
   "x22"; "x23"; "x24"; "x25"; "x26"; "x27"].

Definition writeSuccessSuffixBooleanCallerRegisters : list string :=
  ["x12"; "x13"; "x14"; "x15"; "x16"; "x17"] ++
  tmp_registers.

Definition writeSuccessSuffixBooleanReturnCallerRegisters : list string :=
  "x1" :: writeSuccessSuffixBooleanCallerRegisters.

Definition writeSuccessSuffixBoolean159a0CallPost
    `{!islaG Sigma} `{!threadG} (sp : bv 64) (tail : spec)
    (saved : list valu) : iProp Sigma :=
  (reg_col zesu_ram_sys_regs ∗
   reg_col ((fun r => (KindReg r, BitsShape 64)) <$>
     writeSuccessSuffixBooleanReturnCallerRegisters) ∗
   reg_col (zip_with (fun r v => (KindReg r, ExactShape v))
     writeSuccessSuffixBooleanSavedRegisters saved) ∗
   "x2" ↦ᵣ RVal_Bits sp ∗
   "x10" ↦ᵣ: (fun r => ⌜valu_has_shape r (BitsShape 64)⌝) ∗
   "x11" ↦ᵣ: (fun r => ⌜valu_has_shape r (BitsShape 64)⌝) ∗
   (bv_unsigned sp - 16) ↦ₘ? 16 ∗
   mmio_range 0x2401a0c0 16 ∗ spec_trace tail ∗ True)%I.

Global Instance : LithiumUnfold (@writeSuccessSuffixBoolean159a0CallPost) := I.

Definition writeSuccessSuffixBoolean1599cCallSpec
    `{!islaG Sigma} `{!threadG} (Q : iProp Sigma) : iProp Sigma :=
  (∃ (sp value : bv 64) (tail : spec) (saved : list valu),
    reg_col zesu_ram_sys_regs ∗
    reg_col ((fun r => (KindReg r, BitsShape 64)) <$>
      writeSuccessSuffixBooleanCallerRegisters) ∗
    reg_col (zip_with (fun r v => (KindReg r, ExactShape v))
      writeSuccessSuffixBooleanSavedRegisters saved) ∗
    ⌜length saved = 12%nat⌝ ∗
    ⌜Forall (fun v => valu_has_shape v (BitsShape 64)) saved⌝ ∗
    "x1" ↦ᵣ RVal_Bits (BV 64 0x15998) ∗
    "x2" ↦ᵣ RVal_Bits sp ∗
    "x10" ↦ᵣ RVal_Bits value ∗
    "x11" ↦ᵣ: (fun r => ⌜valu_has_shape r (BitsShape 64)⌝) ∗
    (bv_unsigned sp - 16) ↦ₘ? 16 ∗
    mmio_range 0x2401a0c0 16 ∗
    spec_trace (writeOutputEvents (sp - BV 64 9)%bv (BV 64 1) tail) ∗
    ⌜bv_unsigned sp `mod` 16 = 0⌝ ∗
    ⌜0x20000000 <= bv_unsigned sp - 16⌝ ∗
    ⌜bv_unsigned sp < 0x40000000⌝ ∗
    instr_pre 0x159a0
      (writeSuccessSuffixBoolean159a0CallPost sp tail saved ∗ Q) ∗
    Q)%I.

Global Instance : LithiumUnfold (@writeSuccessSuffixBoolean1599cCallSpec) := I.

Lemma write_success_suffix_boolean_1599c_call
    `{!islaG Sigma} `{!threadG} (Q : iProp Sigma) :
  instr_lookup_resources IslaTraces.write_success_blocks.Index.lookup -∗
  □ instr_pre 0x15b9c zesuEncoderBooleanCallSpec -∗
  instr_body 0x1599c (writeSuccessSuffixBoolean1599cCallSpec Q).
Proof.
  iStartProof. iIntros "#Hlookup #Hboolean".
  iPoseProof "Hlookup" as "#Hlookup1599c".
  iEval (rewrite /instr_lookup_resources) in "Hlookup1599c".
  iPoseProof ("Hlookup1599c" $! 0x1599c with "[]") as "#Hinstr1599c".
  { iPureIntro. rewrite IslaTraces.write_success_blocks.Index.lookup_a1599c.
    done. }
  iPoseProof (IslaTraces.write_success_121.a1599c_spec.a1599c_spec
    0x1599c with "Hinstr1599c") as "Hjalr".
  rewrite instr_pre'_eq. iIntros "Hentry".
  iEval (rewrite /writeSuccessSuffixBoolean1599cCallSpec) in "Hentry".
  iDestruct "Hentry" as (sp value tail saved)
    "(Hsys & Hcaller & Hsaved & %HsavedLength & %HsavedShapes & H1 & H2 &
      H10 & H11 & Hstack & Hmmio & Htrace & %Halign & %Hmin & %Hmax &
      Hpost & HQ)".
  iEval (rewrite /reg_col) in "Hcaller".
  iEval (unfold writeSuccessSuffixBooleanCallerRegisters; cbn) in "Hcaller".
  iDestruct "Hcaller" as
    "(H12 & H13 & H14 & H15 & H16 & H17 & H5 & H6 & H7 & H28 & H29 &
      H30 & H31 & _)".
  destruct saved as [|r8 saved]; cbn in HsavedLength; try lia.
  destruct saved as [|r9 saved]; cbn in HsavedLength; try lia.
  destruct saved as [|r18 saved]; cbn in HsavedLength; try lia.
  destruct saved as [|r19 saved]; cbn in HsavedLength; try lia.
  destruct saved as [|r20 saved]; cbn in HsavedLength; try lia.
  destruct saved as [|r21 saved]; cbn in HsavedLength; try lia.
  destruct saved as [|r22 saved]; cbn in HsavedLength; try lia.
  destruct saved as [|r23 saved]; cbn in HsavedLength; try lia.
  destruct saved as [|r24 saved]; cbn in HsavedLength; try lia.
  destruct saved as [|r25 saved]; cbn in HsavedLength; try lia.
  destruct saved as [|r26 saved]; cbn in HsavedLength; try lia.
  destruct saved as [|r27 saved]; cbn in HsavedLength; try lia.
  destruct saved as [|vrest rest]; cbn in HsavedLength; try lia.
  repeat rewrite Forall_cons_iff in HsavedShapes.
  destruct HsavedShapes as
    (Hr8 & Hr9 & Hr18 & Hr19 & Hr20 & Hr21 & Hr22 & Hr23 & Hr24 & Hr25 &
      Hr26 & Hr27 & _).
  iEval (rewrite /reg_col) in "Hsaved".
  iDestruct "Hsaved" as
    "(H8 & H9 & H18 & H19 & H20 & H21 & H22 & H23 & H24 & H25 & H26 &
      H27 & _)".
  iDestruct "H8" as (v8) "(%Hv8 & H8)".
  iDestruct "H9" as (v9) "(%Hv9 & H9)".
  iDestruct "H18" as (v18) "(%Hv18 & H18)".
  iDestruct "H19" as (v19) "(%Hv19 & H19)".
  iDestruct "H20" as (v20) "(%Hv20 & H20)".
  iDestruct "H21" as (v21) "(%Hv21 & H21)".
  iDestruct "H22" as (v22) "(%Hv22 & H22)".
  iDestruct "H23" as (v23) "(%Hv23 & H23)".
  iDestruct "H24" as (v24) "(%Hv24 & H24)".
  iDestruct "H25" as (v25) "(%Hv25 & H25)".
  iDestruct "H26" as (v26) "(%Hv26 & H26)".
  iDestruct "H27" as (v27) "(%Hv27 & H27)".
  cbn in Hv8, Hv9, Hv18, Hv19, Hv20, Hv21, Hv22, Hv23, Hv24, Hv25, Hv26, Hv27.
  subst v8; subst v9; subst v18; subst v19; subst v20; subst v21.
  subst v22; subst v23; subst v24; subst v25; subst v26; subst v27.
  apply valu_has_bits_shape in Hr8 as (b8 & ->).
  apply valu_has_bits_shape in Hr9 as (b9 & ->).
  apply valu_has_bits_shape in Hr18 as (b18 & ->).
  apply valu_has_bits_shape in Hr19 as (b19 & ->).
  apply valu_has_bits_shape in Hr20 as (b20 & ->).
  apply valu_has_bits_shape in Hr21 as (b21 & ->).
  apply valu_has_bits_shape in Hr22 as (b22 & ->).
  apply valu_has_bits_shape in Hr23 as (b23 & ->).
  apply valu_has_bits_shape in Hr24 as (b24 & ->).
  apply valu_has_bits_shape in Hr25 as (b25 & ->).
  apply valu_has_bits_shape in Hr26 as (b26 & ->).
  apply valu_has_bits_shape in Hr27 as (b27 & ->).
  iApply "Hjalr".
  rewrite /InstrSpecs.Specs.zesu_jalr_same_spec.
  iExists (BV 64 0x15998). iFrame "Hsys H1".
  iSplit; first (iPureIntro; bv_solve).
  have Htarget :
      bv_unsigned
        (bv_or (bv_and ((BV 64 0x15998) + BV 64 516)%bv
          (BV 64 18446744073709551614)) (BV 64 0)) = 0x15b9c by
    bv_solve.
  rewrite Htarget.
  iEval (rewrite -instr_pre'_eq) in "Hboolean".
  iApply (instr_pre_wand 0x15b9c 0x15b9c true true with "Hboolean");
    [done | reflexivity |].
  iIntros "Hcall".
  iEval (unfold zesuEncoderBooleanCallSpec, zesu_c_call).
  iExists sp, (BV 64 0x159a0).
  have HreturnAddress : Z_to_bv 64 (0x1599c + 4) = BV 64 0x159a0 by
    bv_solve.
  rewrite HreturnAddress.
  iDestruct "Hcall" as "(HsysCall & Hret & _)".
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
  iEval (rewrite reg_mapsto_pred_eq /reg_mapsto_pred_def) in "H11".
  iDestruct "H11" as (r11) "(H11 & %Hs11)".
  apply valu_has_bits_shape in Hs11 as (b11 & ->).
  iFrame "HsysCall".
  iEval (rewrite /tmp_registers !reg_col_cons reg_col_nil).
  iFrame "H5 H6 H7 H28 H29 H30 H31".
  iEval (rewrite !reg_mapsto_pred_eq /reg_mapsto_pred_def).
  iEval (simpl).
  iExists (RVal_Bits value); iFrame "H10"; iExists value; iSplit; first done.
  iExists (RVal_Bits b11); iFrame "H11"; iExists b11; iSplit; first done.
  iExists (RVal_Bits b12); iFrame "H12"; iExists b12; iSplit; first done.
  iExists (RVal_Bits b13); iFrame "H13"; iExists b13; iSplit; first done.
  iExists (RVal_Bits b14); iFrame "H14"; iExists b14; iSplit; first done.
  iExists (RVal_Bits b15); iFrame "H15"; iExists b15; iSplit; first done.
  iExists (RVal_Bits b16); iFrame "H16"; iExists b16; iSplit; first done.
  iExists (RVal_Bits b17); iFrame "H17"; iExists b17; iSplit; first done.
  iExists (RVal_Bits b8); iFrame "H8"; iSplit; first done.
  iExists (RVal_Bits b9); iFrame "H9"; iSplit; first done.
  iExists (RVal_Bits b18); iFrame "H18"; iSplit; first done.
  iExists (RVal_Bits b19); iFrame "H19"; iSplit; first done.
  iExists (RVal_Bits b20); iFrame "H20"; iSplit; first done.
  iExists (RVal_Bits b21); iFrame "H21"; iSplit; first done.
  iExists (RVal_Bits b22); iFrame "H22"; iSplit; first done.
  iExists (RVal_Bits b23); iFrame "H23"; iSplit; first done.
  iExists (RVal_Bits b24); iFrame "H24"; iSplit; first done.
  iExists (RVal_Bits b25); iFrame "H25"; iSplit; first done.
  iExists (RVal_Bits b26); iFrame "H26"; iSplit; first done.
  iExists (RVal_Bits b27); iFrame "H27"; iSplit; first done.
  iFrame "H2 Hstack".
  repeat iSplit; try iPureIntro; try bv_solve; try lia.
  liARun.
  Unshelve. all: prepare_sidecond.
  all: try assumption; try bv_solve; try lia; try iFrame.
  Unshelve. all: try iFrame.
  all: iExists tail.
  all: iFrame "Hmmio Htrace".
  all: repeat iSplit; try iPureIntro; try assumption; try lia.
  all: iApply (instr_pre_wand 88480 88480 true true with "Hpost");
    [done | reflexivity |].
  all: iIntros "Hpost".
  all: iEval (unfold writeSuccessSuffixBoolean159a0CallPost) in "Hpost".
  all: iEval (unfold writeSuccessSuffixBoolean159a0CallPost).
  all: iFrame "Hpost HQ".
Qed.

