From Coq Require Import ZArith.ZArith.
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Contracts.IslarisMachine.
Require Import ZesuSsz.Experiments.WriteSuccessEvents.
Require Import ZesuSsz.Experiments.WriteSuccessEncoderOptionalU64Call.
Require Import ZesuSsz.Experiments.WriteSuccessCallAbi.
Require Import ZesuSsz.Experiments.WriteSuccessNativeSuffixOptionalU64159b8Defs.
Require Import ZesuSsz.Experiments.WriteSuccessNativeSuffixOptionalU64159b8CallPrefix.
Require Import ZesuSsz.Experiments.WriteSuccessNativeSuffixOptionalU64159b8NoneTag.
Require Import ZesuSsz.Experiments.WriteSuccessNativeSuffixOptionalU64159b8SomePost.

Definition writeSuccessSuffixOptionalU64159b8SomeFrame
    `{!islaG Sigma} `{!threadG} (Q : iProp Sigma)
    (sp ptr value tag : bv 64) (tail : spec) : iProp Sigma :=
  (reg_col ((fun r => (KindReg r, BitsShape 64)) <$> tmp_registers) ∗
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
   bv_unsigned ptr ↦ₘ value ∗
   (bv_unsigned ptr + 8) ↦ₘ tag ∗
   mmio_range 0x2401a0c0 16 ∗
   ⌜bv_unsigned sp `mod` 16 = 0⌝ ∗
   ⌜0x20000000 <= bv_unsigned sp - 32⌝ ∗
   ⌜bv_unsigned sp < 0x40000000⌝ ∗
   ⌜bv_extract 0 3 ptr = BV 3 0⌝ ∗
   ⌜0x20000000 <= bv_unsigned ptr⌝ ∗
   ⌜bv_unsigned ptr + 8 < 0x40000000⌝ ∗
   ⌜bv_extract 0 8 tag <> BV 8 0⌝ ∗
   spec_trace (writeOutputEvents (sp - BV 64 25)%bv (BV 64 1)
     (writeOutputEvents (sp - BV 64 16)%bv (BV 64 8) tail)) ∗
   (∀ (b8 b9 b18 b19 b20 b21 b22 b23 b24 b25 b26 b27 : bv 64),
      instr_pre 0x159bc
        (writeSuccessSuffixOptionalU64159b8Return
          sp ptr value tag tail b8 b9 b18 b19 b20 b21 b22 b23 b24 b25 b26 b27 ∗ Q)) ∗ Q)%I.

Global Instance : LithiumUnfold
    (@writeSuccessSuffixOptionalU64159b8SomeFrame) := I.

Lemma write_success_suffix_optional_u64_159b8_some_assembly
    `{!islaG Sigma} `{!threadG} (Q : iProp Sigma)
    (sp ptr value tag : bv 64) (tail : spec) :
  (reg_col zesu_ram_sys_regs ∗
   "x1" ↦ᵣ RVal_Bits (Z_to_bv 64 (0x159b8 + 4)) ∗ True) -∗
  writeSuccessSuffixOptionalU64159b8SomeFrame Q sp ptr value tag tail -∗
  zesuEncoderOptionalU64CallSpec.
Proof.
  iIntros "(HsysRet & H1Ret & _) Hframe".
  rewrite /writeSuccessSuffixOptionalU64159b8SomeFrame.
  iDestruct "Hframe" as
    "(Htmp & H2 & H10 & H11 & H12 & H13 & H14 & H15 & H16 & H17 & H8 &
      H9 & H18 & H19 & H20 & H21 & H22 & H23 & H24 & H25 & H26 & H27 &
      Hstack & Hvalue & Htag & Hmmio & %HspAlign & %HspLower & %HspUpper &
      %HptrAlign & %HptrLower & %HptrUpper & %HtagNonzero & Htrace & Hret & HQ)".
  iAssert (writeSuccessSuffixOptionalU64159b8RawCallPrefix sp ptr)%I
    with "[HsysRet Htmp H1Ret H2 H10 H11 H12 H13 H14 H15 H16 H17 H8 H9
      H18 H19 H20 H21 H22 H23 H24 H25 H26 H27 Hstack]" as "Hraw".
  { rewrite /writeSuccessSuffixOptionalU64159b8RawCallPrefix.
    iFrame.
    repeat iSplit; try iPureIntro; try assumption; try bv_solve; try lia. }
  iPoseProof (write_success_suffix_optional_u64_159b8_call_prefix sp ptr
    with "Hraw") as "Hprefix".
  iDestruct "Hprefix" as
    (b8 b9 b18 b19 b20 b21 b22 b23 b24 b25 b26 b27) "Hprefix".
  iSpecialize ("Hret" $! b8 b9 b18 b19 b20 b21 b22 b23 b24 b25 b26 b27).
  iDestruct (write_success_suffix_optional_u64_tag_split
    (bv_unsigned ptr + 8) tag with "Htag") as
    (tagTail) "(HtagByte & HtagTail & %HtagShape)".
  iAssert (instr_pre 0x159bc
    (zesu_c_call_ret 32
      [RVal_Bits b8; RVal_Bits b9; RVal_Bits b18; RVal_Bits b19;
       RVal_Bits b20; RVal_Bits b21; RVal_Bits b22; RVal_Bits b23;
       RVal_Bits b24; RVal_Bits b25; RVal_Bits b26; RVal_Bits b27]
      (BV 64 0x159bc) sp
      (fun _ =>
        bv_unsigned ptr ↦ₘ value ∗
        (bv_unsigned ptr + 8) ↦ₘ bv_extract 0 8 tag ∗
        mmio_range 0x2401a0c0 16 ∗ spec_trace tail ∗ True)))%I
    with "[Hret HQ HtagTail]" as "HpostExact".
  { iApply (instr_pre_wand 0x159bc 0x159bc true true with "Hret");
      [done | reflexivity |].
    iIntros "Hreturn".
    iEval (unfold zesu_c_call_ret) in "Hreturn".
    iDestruct "Hreturn" as "(HsysPost & HtmpPost & HsavedPost & HrestPost)".
    iEval (rewrite reg_mapsto_pred_eq /reg_mapsto_pred_def) in "HrestPost".
    iDestruct "HrestPost" as (r10Post) "(H10Post & HrestPost)".
    iDestruct "HrestPost" as (b10Post) "(%Hr10Post & HrestPost)".
    iDestruct "HrestPost" as (r11Post) "(H11Post & HrestPost)".
    iDestruct "HrestPost" as (b11Post)
      "(%Hr11Post & H2Post & HstackPost & Hresources)".
    subst r10Post r11Post.
    iDestruct "Hresources" as
      "(HvaluePost & HtagBytePost & HmmioPost & HtracePost & _)".
    iPoseProof (write_success_suffix_optional_u64_tag_combine
      (bv_unsigned ptr + 8) tag tagTail
      with "HtagBytePost HtagTail []") as "HtagPost".
    { iPureIntro. exact HtagShape. }
    iSplitL "HsysPost HtmpPost HsavedPost H10Post H11Post H2Post HstackPost
      HvaluePost HtagPost HmmioPost HtracePost".
    - rewrite /writeSuccessSuffixOptionalU64159b8Return /zesu_c_call_ret.
      iFrame "HsysPost HtmpPost HsavedPost".
      iEval (rewrite reg_mapsto_pred_eq /reg_mapsto_pred_def).
      iFrame "H10Post". iExists b10Post. iSplit; first done.
      iFrame "H11Post". iExists b11Post. iSplit; first done.
      iFrame "H2Post HstackPost".
      iFrame "HvaluePost HtagPost HmmioPost HtracePost".
    - iExact "HQ". }
  have HtraceAddress :
      (sp - BV 64 25)%bv =
      (sp - BV 64 16 - BV 64 16 + BV 64 7)%bv by bv_solve.
  iEval (rewrite HtraceAddress) in "Htrace".
  iLeft.
  iApply write_success_suffix_optional_u64_159b8_some_post.
  rewrite /writeSuccessSuffixOptionalU64159b8SomePost.
  iFrame "Hprefix Hvalue HtagByte Hmmio Htrace HpostExact".
  repeat iSplit; iPureIntro; assumption.
  Unshelve. all: try prepare_sidecond; try assumption; try bv_solve; try lia; try iFrame.
Qed.
