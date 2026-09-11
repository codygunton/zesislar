Require Import ZesuSsz.Automation.All.
From Coq Require Import ZArith.ZArith.
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Contracts.IslarisMachine.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessCallAbi.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessNativeSuffixOptionalU64159b8Defs.

Definition writeSuccessSuffixOptionalU64159b8RawCallPrefix
    `{!islaG Sigma} `{!threadG} (ret sp ptr : bv 64) : iProp Sigma :=
  (reg_col zesu_ram_sys_regs ∗
   reg_col ((fun r => (KindReg r, BitsShape 64)) <$> tmp_registers) ∗
   "x1" ↦ᵣ RVal_Bits ret ∗
   "x2" ↦ᵣ RVal_Bits sp ∗
   "x10" ↦ᵣ RVal_Bits ptr ∗
   "x11" ↦ᵣ: (fun r => ⌜valu_has_shape r (BitsShape 64)⌝) ∗
   "x12" ↦ᵣ: (fun r => ⌜valu_has_shape r (BitsShape 64)⌝) ∗
   "x13" ↦ᵣ: (fun r => ⌜valu_has_shape r (BitsShape 64)⌝) ∗
   "x14" ↦ᵣ: (fun r => ⌜valu_has_shape r (BitsShape 64)⌝) ∗
   "x15" ↦ᵣ: (fun r => ⌜valu_has_shape r (BitsShape 64)⌝) ∗
   "x16" ↦ᵣ: (fun r => ⌜valu_has_shape r (BitsShape 64)⌝) ∗
   "x17" ↦ᵣ: (fun r => ⌜valu_has_shape r (BitsShape 64)⌝) ∗
   "x8" ↦ᵣ: (fun r => ⌜valu_has_shape r (BitsShape 64)⌝) ∗
   "x9" ↦ᵣ: (fun r => ⌜valu_has_shape r (BitsShape 64)⌝) ∗
   "x18" ↦ᵣ: (fun r => ⌜valu_has_shape r (BitsShape 64)⌝) ∗
   "x19" ↦ᵣ: (fun r => ⌜valu_has_shape r (BitsShape 64)⌝) ∗
   "x20" ↦ᵣ: (fun r => ⌜valu_has_shape r (BitsShape 64)⌝) ∗
   "x21" ↦ᵣ: (fun r => ⌜valu_has_shape r (BitsShape 64)⌝) ∗
   "x22" ↦ᵣ: (fun r => ⌜valu_has_shape r (BitsShape 64)⌝) ∗
   "x23" ↦ᵣ: (fun r => ⌜valu_has_shape r (BitsShape 64)⌝) ∗
   "x24" ↦ᵣ: (fun r => ⌜valu_has_shape r (BitsShape 64)⌝) ∗
   "x25" ↦ᵣ: (fun r => ⌜valu_has_shape r (BitsShape 64)⌝) ∗
   "x26" ↦ᵣ: (fun r => ⌜valu_has_shape r (BitsShape 64)⌝) ∗
   "x27" ↦ᵣ: (fun r => ⌜valu_has_shape r (BitsShape 64)⌝) ∗
   (bv_unsigned sp - 32) ↦ₘ? 32 ∗
   ⌜bv_unsigned sp `mod` 16 = 0⌝ ∗
   ⌜bv_extract 0 1 ret = BV 1 0⌝ ∗
   ⌜bv_extract 1 1 ret = BV 1 0⌝ ∗
   ⌜bv_extract 0 2 ret = BV 2 0⌝ ∗
   ⌜0x20000000 <= bv_unsigned sp - 32⌝ ∗
   ⌜bv_unsigned sp < 0x40000000⌝)%I.

Global Instance : LithiumUnfold
    (@writeSuccessSuffixOptionalU64159b8RawCallPrefix) := I.

Definition writeSuccessSuffixOptionalU64159b8CallPrefixSaved
    `{!islaG Sigma} `{!threadG} (ret sp ptr : bv 64)
    (b8 b9 b18 b19 b20 b21 b22 b23 b24 b25 b26 b27 : bv 64) : iProp Sigma :=
  (reg_col zesu_ram_sys_regs ∗
   reg_col ((fun r => (KindReg r, BitsShape 64)) <$> tmp_registers) ∗
   "x10" ↦ᵣ RVal_Bits ptr ∗
   "x11" ↦ᵣ: (fun r => ⌜valu_has_shape r (BitsShape 64)⌝) ∗
   "x12" ↦ᵣ: (fun r => ⌜valu_has_shape r (BitsShape 64)⌝) ∗
   "x13" ↦ᵣ: (fun r => ⌜valu_has_shape r (BitsShape 64)⌝) ∗
   "x14" ↦ᵣ: (fun r => ⌜valu_has_shape r (BitsShape 64)⌝) ∗
   "x15" ↦ᵣ: (fun r => ⌜valu_has_shape r (BitsShape 64)⌝) ∗
   "x16" ↦ᵣ: (fun r => ⌜valu_has_shape r (BitsShape 64)⌝) ∗
   "x17" ↦ᵣ: (fun r => ⌜valu_has_shape r (BitsShape 64)⌝) ∗
   "x8" ↦ᵣ RVal_Bits b8 ∗ "x9" ↦ᵣ RVal_Bits b9 ∗
   "x18" ↦ᵣ RVal_Bits b18 ∗ "x19" ↦ᵣ RVal_Bits b19 ∗
   "x20" ↦ᵣ RVal_Bits b20 ∗ "x21" ↦ᵣ RVal_Bits b21 ∗
   "x22" ↦ᵣ RVal_Bits b22 ∗ "x23" ↦ᵣ RVal_Bits b23 ∗
   "x24" ↦ᵣ RVal_Bits b24 ∗ "x25" ↦ᵣ RVal_Bits b25 ∗
   "x26" ↦ᵣ RVal_Bits b26 ∗ "x27" ↦ᵣ RVal_Bits b27 ∗
   "x1" ↦ᵣ RVal_Bits ret ∗ "x2" ↦ᵣ RVal_Bits sp ∗
   ⌜bv_unsigned sp `mod` 16 = 0⌝ ∗
   ⌜bv_extract 0 1 ret = BV 1 0⌝ ∗
   ⌜bv_extract 1 1 ret = BV 1 0⌝ ∗
   ⌜bv_extract 0 2 ret = BV 2 0⌝ ∗
   ⌜0x20000000 <= bv_unsigned sp - 32 /\ bv_unsigned sp < 0x40000000⌝ ∗
   (bv_unsigned sp - 32) ↦ₘ? 32)%I.

Global Instance : LithiumUnfold
    (@writeSuccessSuffixOptionalU64159b8CallPrefixSaved) := I.

Lemma write_success_suffix_optional_u64_159b8_call_prefix
    `{!islaG Sigma} `{!threadG} (ret sp ptr : bv 64) :
  writeSuccessSuffixOptionalU64159b8RawCallPrefix ret sp ptr -∗
  ∃ (b8 b9 b18 b19 b20 b21 b22 b23 b24 b25 b26 b27 : bv 64),
    writeSuccessSuffixOptionalU64159b8CallPrefixSaved ret sp ptr
      b8 b9 b18 b19 b20 b21 b22 b23 b24 b25 b26 b27.
Proof.
  iIntros "Hraw".
  rewrite /writeSuccessSuffixOptionalU64159b8RawCallPrefix.
  iDestruct "Hraw" as
    "(Hsys & Htmp & H1 & H2 & H10 & H11 & H12 & H13 & H14 & H15 & H16 &
      H17 & H8 & H9 & H18 & H19 & H20 & H21 & H22 & H23 & H24 & H25 &
      H26 & H27 & Hstack & %HspAlign & %Hret0 & %Hret1 & %Hret2 &
      %HspLower & %HspUpper)".
  iEval (rewrite !reg_mapsto_pred_eq /reg_mapsto_pred_def) in
    "H11 H12 H13 H14 H15 H16 H17 H8 H9 H18 H19 H20 H21 H22 H23 H24 H25
      H26 H27".
  iDestruct "H11" as (r11) "(H11 & %Hs11)".
  iDestruct "H12" as (r12) "(H12 & %Hs12)".
  iDestruct "H13" as (r13) "(H13 & %Hs13)".
  iDestruct "H14" as (r14) "(H14 & %Hs14)".
  iDestruct "H15" as (r15) "(H15 & %Hs15)".
  iDestruct "H16" as (r16) "(H16 & %Hs16)".
  iDestruct "H17" as (r17) "(H17 & %Hs17)".
  iDestruct "H8" as (r8) "(H8 & %Hs8)".
  iDestruct "H9" as (r9) "(H9 & %Hs9)".
  iDestruct "H18" as (r18) "(H18 & %Hs18)".
  iDestruct "H19" as (r19) "(H19 & %Hs19)".
  iDestruct "H20" as (r20) "(H20 & %Hs20)".
  iDestruct "H21" as (r21) "(H21 & %Hs21)".
  iDestruct "H22" as (r22) "(H22 & %Hs22)".
  iDestruct "H23" as (r23) "(H23 & %Hs23)".
  iDestruct "H24" as (r24) "(H24 & %Hs24)".
  iDestruct "H25" as (r25) "(H25 & %Hs25)".
  iDestruct "H26" as (r26) "(H26 & %Hs26)".
  iDestruct "H27" as (r27) "(H27 & %Hs27)".
  apply valu_has_bits_shape in Hs11 as (b11 & ->).
  apply valu_has_bits_shape in Hs12 as (b12 & ->).
  apply valu_has_bits_shape in Hs13 as (b13 & ->).
  apply valu_has_bits_shape in Hs14 as (b14 & ->).
  apply valu_has_bits_shape in Hs15 as (b15 & ->).
  apply valu_has_bits_shape in Hs16 as (b16 & ->).
  apply valu_has_bits_shape in Hs17 as (b17 & ->).
  apply valu_has_bits_shape in Hs8 as (b8 & ->).
  apply valu_has_bits_shape in Hs9 as (b9 & ->).
  apply valu_has_bits_shape in Hs18 as (b18 & ->).
  apply valu_has_bits_shape in Hs19 as (b19 & ->).
  apply valu_has_bits_shape in Hs20 as (b20 & ->).
  apply valu_has_bits_shape in Hs21 as (b21 & ->).
  apply valu_has_bits_shape in Hs22 as (b22 & ->).
  apply valu_has_bits_shape in Hs23 as (b23 & ->).
  apply valu_has_bits_shape in Hs24 as (b24 & ->).
  apply valu_has_bits_shape in Hs25 as (b25 & ->).
  apply valu_has_bits_shape in Hs26 as (b26 & ->).
  apply valu_has_bits_shape in Hs27 as (b27 & ->).
  iExists b8, b9, b18, b19, b20, b21, b22, b23, b24, b25, b26, b27.
  rewrite /writeSuccessSuffixOptionalU64159b8CallPrefixSaved.
  iAssert ("x11" ↦ᵣ: (fun r => ⌜valu_has_shape r (BitsShape 64)⌝))%I
    with "[H11]" as "H11bits".
  { rewrite reg_mapsto_pred_eq /reg_mapsto_pred_def.
    iExists (RVal_Bits b11). iFrame "H11". iPureIntro. cbn. done. }
  iAssert ("x12" ↦ᵣ: (fun r => ⌜valu_has_shape r (BitsShape 64)⌝))%I
    with "[H12]" as "H12bits".
  { rewrite reg_mapsto_pred_eq /reg_mapsto_pred_def.
    iExists (RVal_Bits b12). iFrame "H12". iPureIntro. cbn. done. }
  iAssert ("x13" ↦ᵣ: (fun r => ⌜valu_has_shape r (BitsShape 64)⌝))%I
    with "[H13]" as "H13bits".
  { rewrite reg_mapsto_pred_eq /reg_mapsto_pred_def.
    iExists (RVal_Bits b13). iFrame "H13". iPureIntro. cbn. done. }
  iAssert ("x14" ↦ᵣ: (fun r => ⌜valu_has_shape r (BitsShape 64)⌝))%I
    with "[H14]" as "H14bits".
  { rewrite reg_mapsto_pred_eq /reg_mapsto_pred_def.
    iExists (RVal_Bits b14). iFrame "H14". iPureIntro. cbn. done. }
  iAssert ("x15" ↦ᵣ: (fun r => ⌜valu_has_shape r (BitsShape 64)⌝))%I
    with "[H15]" as "H15bits".
  { rewrite reg_mapsto_pred_eq /reg_mapsto_pred_def.
    iExists (RVal_Bits b15). iFrame "H15". iPureIntro. cbn. done. }
  iAssert ("x16" ↦ᵣ: (fun r => ⌜valu_has_shape r (BitsShape 64)⌝))%I
    with "[H16]" as "H16bits".
  { rewrite reg_mapsto_pred_eq /reg_mapsto_pred_def.
    iExists (RVal_Bits b16). iFrame "H16". iPureIntro. cbn. done. }
  iAssert ("x17" ↦ᵣ: (fun r => ⌜valu_has_shape r (BitsShape 64)⌝))%I
    with "[H17]" as "H17bits".
  { rewrite reg_mapsto_pred_eq /reg_mapsto_pred_def.
    iExists (RVal_Bits b17). iFrame "H17". iPureIntro. cbn. done. }
  iFrame "Hsys Htmp H10 H11bits H12bits H13bits H14bits H15bits H16bits
    H17bits H8 H9 H18 H19 H20 H21 H22 H23 H24 H25 H26 H27".
  iFrame "H1 H2 Hstack".
  repeat iSplit; iPureIntro; assumption || lia.
Qed.
