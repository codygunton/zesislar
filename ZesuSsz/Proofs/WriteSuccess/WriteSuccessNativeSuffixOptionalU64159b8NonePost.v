Require Import ZesuSsz.Automation.All.
From Coq Require Import ZArith.ZArith.
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessEvents.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessEncoderOptionalU64Call.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessCallAbi.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessNativeSuffixOptionalU64159b8Defs.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessNativeSuffixOptionalU64159b8CallPrefix.

Definition writeSuccessSuffixOptionalU64159b8NonePost
    `{!islaG Sigma} `{!threadG}
    (ret sp ptr value : bv 64) (tag : bv 8) (tail : spec)
    (b8 b9 b18 b19 b20 b21 b22 b23 b24 b25 b26 b27 : bv 64) : iProp Sigma :=
  (writeSuccessSuffixOptionalU64159b8CallPrefixSaved ret sp ptr
     b8 b9 b18 b19 b20 b21 b22 b23 b24 b25 b26 b27 ∗
   bv_unsigned ptr ↦ₘ value ∗
   (bv_unsigned ptr + 8) ↦ₘ tag ∗ ⌜tag = BV 8 0⌝ ∗
   ⌜bv_extract 0 3 ptr = BV 3 0⌝ ∗
   ⌜0x20000000 <= bv_unsigned ptr⌝ ∗
   ⌜bv_unsigned ptr + 8 < 0x40000000⌝ ∗
   mmio_range 0x2401a0c0 16 ∗
   spec_trace (writeOutputEventsAny (sp - BV 64 9)%bv (BV 64 1) tail) ∗
   instr_pre (bv_unsigned ret)
     (zesu_c_call_ret 32
       [RVal_Bits b8; RVal_Bits b9; RVal_Bits b18; RVal_Bits b19;
        RVal_Bits b20; RVal_Bits b21; RVal_Bits b22; RVal_Bits b23;
        RVal_Bits b24; RVal_Bits b25; RVal_Bits b26; RVal_Bits b27]
       ret sp
       (fun _ =>
         bv_unsigned ptr ↦ₘ value ∗
         (bv_unsigned ptr + 8) ↦ₘ tag ∗
         mmio_range 0x2401a0c0 16 ∗ spec_trace tail ∗ True)))%I.

Global Instance : LithiumUnfold
    (@writeSuccessSuffixOptionalU64159b8NonePost) := I.

Lemma write_success_suffix_optional_u64_159b8_none_post
    `{!islaG Sigma} `{!threadG}
    (ret sp ptr value : bv 64) (tag : bv 8) (tail : spec)
    (b8 b9 b18 b19 b20 b21 b22 b23 b24 b25 b26 b27 : bv 64) :
  writeSuccessSuffixOptionalU64159b8NonePost ret sp ptr value tag tail
    b8 b9 b18 b19 b20 b21 b22 b23 b24 b25 b26 b27 -∗
  zesuEncoderOptionalU64NoneCallSpec.
Proof.
  rewrite /writeSuccessSuffixOptionalU64159b8NonePost.
  iIntros "(Hsaved & Hvalue & Htag & %HtagZero & %HptrAlign & %HptrLower &
    %HptrUpper & Hmmio & Htrace & Hpost)".
  iEval (rewrite /writeSuccessSuffixOptionalU64159b8CallPrefixSaved) in "Hsaved".
  iDestruct "Hsaved" as
    "(Hsys & Htmp & H10 & H11 & H12 & H13 & H14 & H15 & H16 & H17 & H8 &
      H9 & H18 & H19 & H20 & H21 & H22 & H23 & H24 & H25 & H26 & H27 &
      H1 & H2 & %HspAlign & %Hret0 & %Hret1 & %Hret2 & %Hbounds & Hstack)".
  iEval (rewrite !reg_mapsto_pred_eq /reg_mapsto_pred_def) in
    "H11 H12 H13 H14 H15 H16 H17".
  iDestruct "H11" as (r11) "(H11 & %Hs11)".
  iDestruct "H12" as (r12) "(H12 & %Hs12)".
  iDestruct "H13" as (r13) "(H13 & %Hs13)".
  iDestruct "H14" as (r14) "(H14 & %Hs14)".
  iDestruct "H15" as (r15) "(H15 & %Hs15)".
  iDestruct "H16" as (r16) "(H16 & %Hs16)".
  iDestruct "H17" as (r17) "(H17 & %Hs17)".
  apply valu_has_bits_shape in Hs11 as (b11 & ->).
  apply valu_has_bits_shape in Hs12 as (b12 & ->).
  apply valu_has_bits_shape in Hs13 as (b13 & ->).
  apply valu_has_bits_shape in Hs14 as (b14 & ->).
  apply valu_has_bits_shape in Hs15 as (b15 & ->).
  apply valu_has_bits_shape in Hs16 as (b16 & ->).
  apply valu_has_bits_shape in Hs17 as (b17 & ->).
  rewrite /zesuEncoderOptionalU64NoneCallSpec /zesu_c_call.
  iExists sp, ret. iFrame "Hsys Htmp".
  iEval (rewrite !reg_mapsto_pred_eq /reg_mapsto_pred_def; simpl).
  iExists (RVal_Bits ptr). iFrame "H10". iExists ptr. iSplit; first done.
  iExists (RVal_Bits b11). iFrame "H11". iExists b11. iSplit; first done.
  iExists (RVal_Bits b12). iFrame "H12". iExists b12. iSplit; first done.
  iExists (RVal_Bits b13). iFrame "H13". iExists b13. iSplit; first done.
  iExists (RVal_Bits b14). iFrame "H14". iExists b14. iSplit; first done.
  iExists (RVal_Bits b15). iFrame "H15". iExists b15. iSplit; first done.
  iExists (RVal_Bits b16). iFrame "H16". iExists b16. iSplit; first done.
  iExists (RVal_Bits b17). iFrame "H17". iExists b17. iSplit; first done.
  iExists (RVal_Bits b8). iFrame "H8". iSplit; first done.
  iExists (RVal_Bits b9). iFrame "H9". iSplit; first done.
  iExists (RVal_Bits b18). iFrame "H18". iSplit; first done.
  iExists (RVal_Bits b19). iFrame "H19". iSplit; first done.
  iExists (RVal_Bits b20). iFrame "H20". iSplit; first done.
  iExists (RVal_Bits b21). iFrame "H21". iSplit; first done.
  iExists (RVal_Bits b22). iFrame "H22". iSplit; first done.
  iExists (RVal_Bits b23). iFrame "H23". iSplit; first done.
  iExists (RVal_Bits b24). iFrame "H24". iSplit; first done.
  iExists (RVal_Bits b25). iFrame "H25". iSplit; first done.
  iExists (RVal_Bits b26). iFrame "H26". iSplit; first done.
  iExists (RVal_Bits b27). iFrame "H27". iSplit; first done.
  iFrame "H1 H2 Hstack".
  repeat iSplit; try iPureIntro; try assumption; try bv_solve; try lia.
  iExists value, tag, tail.
  iFrame "Hvalue Htag Hmmio Htrace Hpost".
  iPureIntro. repeat split; assumption.
Qed.
