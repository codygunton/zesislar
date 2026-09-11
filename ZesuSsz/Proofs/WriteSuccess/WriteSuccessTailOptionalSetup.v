Require Import ZesuSsz.Automation.All.
Require Import isla.riscv64.riscv64.
From IslaTraces.write_success_blocks Require Import Index.
Require Import ZesuSsz.Contracts.IslarisCode.
Require Import ZesuSsz.Contracts.IslarisMachine.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessEvents.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessNativeSuffixOptionalU64159b8Defs.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessNativeSuffixOptionalU64159b8.

Definition writeSuccessTailOptionalSetupSpec
    `{!islaG Sigma} `{!threadG} (Q : iProp Sigma) : iProp Sigma :=
  (∃ (sp value tag : bv 64) (tail : spec),
    reg_col zesu_ram_sys_regs ∗
    reg_col ((fun r => (KindReg r, BitsShape 64)) <$> tmp_registers) ∗
    "x1" ↦ᵣ: (fun r => ⌜valu_has_shape r (BitsShape 64)⌝) ∗
    "x2" ↦ᵣ RVal_Bits sp ∗
    "x10" ↦ᵣ: (fun r => ⌜valu_has_shape r (BitsShape 64)⌝) ∗
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
    (bv_unsigned sp + 296) ↦ₘ value ∗
    (bv_unsigned sp + 304) ↦ₘ tag ∗
    mmio_range 0x2401a0c0 16 ∗
    ⌜bv_unsigned sp `mod` 16 = 0⌝ ∗
    ⌜0x20000000 <= bv_unsigned sp - 32⌝ ∗
    ⌜bv_unsigned sp < 0x40000000⌝ ∗
    ⌜bv_unsigned sp + 304 < 0x40000000⌝ ∗
    ((⌜bv_extract 0 8 tag = BV 8 0⌝ ∗
       spec_trace (writeOutputEventsAny (sp - BV 64 9)%bv (BV 64 1) tail)) ∨
     (⌜bv_extract 0 8 tag <> BV 8 0⌝ ∗
       spec_trace (writeOutputEventsAny (sp - BV 64 25)%bv (BV 64 1)
         (writeOutputEventsAny (sp - BV 64 16)%bv (BV 64 8) tail)))) ∗
    (∀ b8 b9 b18 b19 b20 b21 b22 b23 b24 b25 b26 b27,
      instr_pre 0x159bc
        (writeSuccessSuffixOptionalU64159b8Return
          (BV 64 0x159bc) sp (sp + BV 64 296)%bv value tag tail
          b8 b9 b18 b19 b20 b21 b22 b23 b24 b25 b26 b27 ∗ Q)) ∗ Q)%I.

Global Instance : LithiumUnfold (@writeSuccessTailOptionalSetupSpec) := I.

Lemma block_159b0 `{!islaG Sigma} `{!threadG} (Q : iProp Sigma) :
  instr_lookup_resources IslaTraces.write_success_blocks.Index.lookup -∗
  instr_body 0x159b8 (writeSuccessSuffixOptionalU64159b8Spec Q) -∗
  instr_body 0x159b0 (writeSuccessTailOptionalSetupSpec Q).
Proof.
  move => *.
  iStartProof. iIntros "_ #Hlookup Hnext".
  liARun.
  Unshelve. all: try zesu_finish.
  Unshelve. all: try zesu_pack (tail, tt)ₗ.
  all: lazymatch goal with |- ?G => fail "block_159b0 residual" G end.
Qed.

Print Assumptions block_159b0.
