Require Import ZesuSsz.Automation.AllLegacy.
Require Import ZesuMachineMap.Machine.
Require Import isla.riscv64.riscv64.
From IslaTraces.write_success_blocks Require Import Index.
Require Import ZesuSsz.Contracts.IslarisCode.
Require Import ZesuSsz.Contracts.IslarisMachine.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessEvents.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessEncoderOptionalU64Call.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessNativeSuffixOptionalU64159b8Defs.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessNativeSuffixOptionalU64159b8Some.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessNativeSuffixOptionalU64159b8None.

Definition writeSuccessSuffixOptionalU64159b8Spec
    `{!islaG Sigma} `{!threadG} (Q : iProp Sigma) : iProp Sigma :=
  (∃ (sp ptr value tag : bv 64) (tail : spec),
    reg_col zesu_ram_sys_regs ∗
    reg_col ((fun r => (KindReg r, BitsShape 64)) <$> tmp_registers) ∗
    "x1" ↦ᵣ RVal_Bits (BV 64 0x159b4) ∗
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
    bv_unsigned ptr ↦ₘ value ∗ (bv_unsigned ptr + 8) ↦ₘ tag ∗
    mmio_range (machineOutputAddress defaultMap) 16 ∗
    ⌜bv_unsigned sp `mod` 16 = 0⌝ ∗
    ⌜(mapRamBase defaultMap) <= bv_unsigned sp - 32⌝ ∗
    ⌜bv_unsigned sp < (machineRamEnd defaultMap)⌝ ∗
    ⌜bv_extract 0 3 ptr = BV 3 0⌝ ∗
    ⌜(mapRamBase defaultMap) <= bv_unsigned ptr⌝ ∗
    ⌜bv_unsigned ptr + 8 < (machineRamEnd defaultMap)⌝ ∗
    (⌜bv_extract 0 8 tag = BV 8 0⌝ ∗
      spec_trace (writeOutputEventsAny (sp - BV 64 9)%bv (BV 64 1) tail) ∨
     ⌜bv_extract 0 8 tag <> BV 8 0⌝ ∗
      spec_trace (writeOutputEventsAny (sp - BV 64 25)%bv (BV 64 1)
        (writeOutputEventsAny (sp - BV 64 16)%bv (BV 64 8) tail))) ∗
    (∀ b8 b9 b18 b19 b20 b21 b22 b23 b24 b25 b26 b27,
      instr_pre 0x159bc
        (writeSuccessSuffixOptionalU64159b8Return
          (BV 64 0x159bc) sp ptr value tag tail b8 b9 b18 b19 b20 b21 b22
          b23 b24 b25 b26 b27 ∗ Q)) ∗ Q)%I.

Global Instance : LithiumUnfold (@writeSuccessSuffixOptionalU64159b8Spec) := I.

Lemma write_success_suffix_optional_u64_159b8
    `{!islaG Sigma} `{!threadG} (Q : iProp Sigma) :
  instr_lookup_resources IslaTraces.write_success_blocks.Index.lookup -∗
  □ instr_pre 0x15bc8 zesuEncoderOptionalU64CallSpec -∗
  instr_body 0x159b8 (writeSuccessSuffixOptionalU64159b8Spec Q).
Proof.
  iStartProof. iIntros "#Hlookup #Hoptional".
  iPoseProof (write_success_suffix_optional_u64_159b8_some Q
    with "Hlookup Hoptional") as "Hsome".
  iPoseProof (write_success_suffix_optional_u64_159b8_none Q
    with "Hlookup Hoptional") as "Hnone".
  rewrite instr_pre'_eq. iIntros "Hentry".
  iEval (rewrite /writeSuccessSuffixOptionalU64159b8Spec) in "Hentry".
  iDestruct "Hentry" as (sp ptr value tag tail)
    "(Hsys & Htmp & H1 & H2 & H10 & H11 & H12 & H13 & H14 & H15 & H16 & H17 &
      H8 & H9 & H18 & H19 & H20 & H21 & H22 & H23 & H24 & H25 & H26 & H27 &
      Hstack & Hvalue & Htag & Hmmio & %HspAlign & %HspLower & %HspUpper &
      %HptrAlign & %HptrLower & %HptrUpper & Hbranch & Hret & HQ)".
  iDestruct "Hbranch" as "[[%Hzero Htrace]|[%Hnonzero Htrace]]".
  - iApply "Hnone".
    iEval (rewrite /writeSuccessSuffixOptionalU64159b8NoneSpec).
    iExists sp, ptr, value, tag, tail.
    iFrame "Hsys Htmp H1 H2 H10 H11 H12 H13 H14 H15 H16 H17 H8 H9 H18 H19
      H20 H21 H22 H23 H24 H25 H26 H27 Hstack Hvalue Htag Hmmio Htrace Hret HQ".
    repeat iSplit; try iPureIntro; try assumption; try bv_solve; try lia.
  - iApply "Hsome".
    iEval (rewrite /writeSuccessSuffixOptionalU64159b8SomeSpec).
    iExists sp, ptr, value, tag, tail.
    iFrame "Hsys Htmp H1 H2 H10 H11 H12 H13 H14 H15 H16 H17 H8 H9 H18 H19
      H20 H21 H22 H23 H24 H25 H26 H27 Hstack Hvalue Htag Hmmio Htrace Hret HQ".
    repeat iSplit; try iPureIntro; try assumption; try bv_solve; try lia.
Qed.
