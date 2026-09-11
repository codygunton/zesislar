Require Import ZesuSsz.Automation.All.
From Coq Require Import Lists.List ZArith.ZArith.
Require Import isla.riscv64.riscv64.
From IslaTraces.write_success_blocks Require Import Index.
From IslaTraces.write_success_123 Require Import a159b8_spec.
Require Import ZesuSsz.Contracts.IslarisCode.
Require Import ZesuSsz.Contracts.IslarisMachine.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessEvents.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessEncoderOptionalU64Call.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessCallAbi.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessNativeSuffixOptionalU64159b8Defs.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessNativeSuffixOptionalU64159b8SomeAssembly.

Definition writeSuccessSuffixOptionalU64159b8SomeSpec
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
    spec_trace (writeOutputEventsAny (sp - BV 64 25)%bv (BV 64 1)
      (writeOutputEventsAny (sp - BV 64 16)%bv (BV 64 8) tail)) ∗
    (∀ (b8 b9 b18 b19 b20 b21 b22 b23 b24 b25 b26 b27 : bv 64),
      instr_pre 0x159bc
        (writeSuccessSuffixOptionalU64159b8Return
          (BV 64 0x159bc) sp ptr value tag tail b8 b9 b18 b19 b20 b21 b22
          b23 b24 b25 b26 b27 ∗ Q)) ∗ Q)%I.

Global Instance : LithiumUnfold
    (@writeSuccessSuffixOptionalU64159b8SomeSpec) := I.

Lemma write_success_suffix_optional_u64_159b8_some
    `{!islaG Sigma} `{!threadG} (Q : iProp Sigma) :
  instr_lookup_resources IslaTraces.write_success_blocks.Index.lookup -∗
  □ instr_pre 0x15bc8 zesuEncoderOptionalU64CallSpec -∗
  instr_body 0x159b8 (writeSuccessSuffixOptionalU64159b8SomeSpec Q).
Proof.
  iStartProof. iIntros "#Hlookup #Hoptional".
  iPoseProof "Hlookup" as "#Hlookup159b8".
  iEval (rewrite /instr_lookup_resources) in "Hlookup159b8".
  iPoseProof ("Hlookup159b8" $! 0x159b8 with "[]") as "#Hinstr159b8".
  { iPureIntro. rewrite IslaTraces.write_success_blocks.Index.lookup_a159b8. done. }
  iPoseProof (IslaTraces.write_success_123.a159b8_spec.a159b8_spec
    0x159b8 with "Hinstr159b8") as "Hjalrx".
  rewrite instr_pre'_eq. iIntros "Hentry".
  iEval (rewrite /writeSuccessSuffixOptionalU64159b8SomeSpec) in "Hentry".
  iDestruct "Hentry" as (sp ptr value tag tail)
    "(Hsys & Htmp & H1 & H2 & H10 & H11 & H12 & H13 & H14 & H15 & H16 & H17 &
      H8 & H9 & H18 & H19 & H20 & H21 & H22 & H23 & H24 & H25 & H26 & H27 &
      Hstack & Hvalue & Htag & Hmmio & %HspAlign & %HspLower & %HspUpper &
      %HptrAlign & %HptrLower & %HptrUpper & %HtagNonzero & Htrace & Hret & HQ)".
  iAssert (writeSuccessSuffixOptionalU64159b8SomeFrame
      Q (BV 64 0x159bc) sp ptr value tag tail)%I
    with "[Htmp H2 H10 H11 H12 H13 H14 H15 H16 H17 H8 H9 H18 H19 H20
      H21 H22 H23 H24 H25 H26 H27 Hstack Hvalue Htag Hmmio Htrace Hret HQ]"
    as "Hframe".
  { rewrite /writeSuccessSuffixOptionalU64159b8SomeFrame. iFrame.
    repeat iSplit; try iPureIntro; try assumption; try bv_solve. }
  iApply "Hjalrx".
  rewrite /InstrSpecs.Specs.zesu_jalr_same_spec.
  iExists (BV 64 0x159b4); iFrame "Hsys H1".
  iSplit; first (iPureIntro; bv_solve).
  have Htargetx :
      bv_unsigned
        (bv_or (bv_and ((BV 64 0x159b4) + BV 64 532)%bv
          (BV 64 18446744073709551614)) (BV 64 0)) = 0x15bc8 by bv_solve.
  rewrite Htargetx.
  iEval (rewrite -instr_pre'_eq) in "Hoptional".
  iApply (instr_pre_wand 0x15bc8 0x15bc8 true true with "Hoptional");
    [done | done |].
  iIntros "Hcall".
  iApply (write_success_suffix_optional_u64_159b8_some_assembly
    Q (BV 64 0x159bc) sp ptr value tag tail with "Hcall Hframe").
Qed.
