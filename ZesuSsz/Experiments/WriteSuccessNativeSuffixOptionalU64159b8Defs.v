From Coq Require Import Lists.List ZArith.ZArith.
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Contracts.IslarisMachine.
Require Import ZesuSsz.Experiments.WriteSuccessEvents.
Require Import ZesuSsz.Experiments.WriteSuccessCallAbi.

Definition writeSuccessSuffixOptionalU64159b8Return
    `{!islaG Sigma} `{!threadG}
    (sp ptr value tag : bv 64) (tail : spec)
    (b8 b9 b18 b19 b20 b21 b22 b23 b24 b25 b26 b27 : bv 64) : iProp Sigma :=
  zesu_c_call_ret 32
    [RVal_Bits b8; RVal_Bits b9; RVal_Bits b18; RVal_Bits b19;
     RVal_Bits b20; RVal_Bits b21; RVal_Bits b22; RVal_Bits b23;
     RVal_Bits b24; RVal_Bits b25; RVal_Bits b26; RVal_Bits b27]
    (BV 64 0x159bc) sp
    (fun _ =>
      bv_unsigned ptr ↦ₘ value ∗
      (bv_unsigned ptr + 8) ↦ₘ tag ∗
      mmio_range 0x2401a0c0 16 ∗ spec_trace tail ∗ True)%I.

Global Instance : LithiumUnfold
    (@writeSuccessSuffixOptionalU64159b8Return) := I.

Definition writeSuccessSuffixOptionalU64159b8CallPrefix
    `{!islaG Sigma} `{!threadG}
    (sp ptr : bv 64) : iProp Sigma :=
  (reg_col zesu_ram_sys_regs ∗
   reg_col ((fun r => (KindReg r, BitsShape 64)) <$> tmp_registers) ∗
   "x10" ↦ᵣ: fun r10 => ∃ b10 : bv 64,
     ⌜r10 = RVal_Bits b10⌝ ∗
   "x11" ↦ᵣ: fun r11 => ∃ b11 : bv 64,
     ⌜r11 = RVal_Bits b11⌝ ∗
   "x12" ↦ᵣ: fun r12 => ∃ b12 : bv 64,
     ⌜r12 = RVal_Bits b12⌝ ∗
   "x13" ↦ᵣ: fun r13 => ∃ b13 : bv 64,
     ⌜r13 = RVal_Bits b13⌝ ∗
   "x14" ↦ᵣ: fun r14 => ∃ b14 : bv 64,
     ⌜r14 = RVal_Bits b14⌝ ∗
   "x15" ↦ᵣ: fun r15 => ∃ b15 : bv 64,
     ⌜r15 = RVal_Bits b15⌝ ∗
   "x16" ↦ᵣ: fun r16 => ∃ b16 : bv 64,
     ⌜r16 = RVal_Bits b16⌝ ∗
   "x17" ↦ᵣ: fun r17 => ∃ b17 : bv 64,
     ⌜r17 = RVal_Bits b17⌝ ∗
   "x8" ↦ᵣ: fun r8 => ⌜valu_has_shape r8 (BitsShape 64)⌝ ∗
   "x9" ↦ᵣ: fun r9 => ⌜valu_has_shape r9 (BitsShape 64)⌝ ∗
   "x18" ↦ᵣ: fun r18 => ⌜valu_has_shape r18 (BitsShape 64)⌝ ∗
   "x19" ↦ᵣ: fun r19 => ⌜valu_has_shape r19 (BitsShape 64)⌝ ∗
   "x20" ↦ᵣ: fun r20 => ⌜valu_has_shape r20 (BitsShape 64)⌝ ∗
   "x21" ↦ᵣ: fun r21 => ⌜valu_has_shape r21 (BitsShape 64)⌝ ∗
   "x22" ↦ᵣ: fun r22 => ⌜valu_has_shape r22 (BitsShape 64)⌝ ∗
   "x23" ↦ᵣ: fun r23 => ⌜valu_has_shape r23 (BitsShape 64)⌝ ∗
   "x24" ↦ᵣ: fun r24 => ⌜valu_has_shape r24 (BitsShape 64)⌝ ∗
   "x25" ↦ᵣ: fun r25 => ⌜valu_has_shape r25 (BitsShape 64)⌝ ∗
   "x26" ↦ᵣ: fun r26 => ⌜valu_has_shape r26 (BitsShape 64)⌝ ∗
   "x27" ↦ᵣ: fun r27 => ⌜valu_has_shape r27 (BitsShape 64)⌝ ∗
   "x1" ↦ᵣ RVal_Bits (BV 64 0x159bc) ∗
   "x2" ↦ᵣ RVal_Bits sp ∗
   ⌜bv_unsigned sp `mod` 16 = 0⌝ ∗
   ⌜bv_extract 0 1 (BV 64 0x159bc) = BV 1 0⌝ ∗
   ⌜bv_extract 1 1 (BV 64 0x159bc) = BV 1 0⌝ ∗
   ⌜bv_extract 0 2 (BV 64 0x159bc) = BV 2 0⌝ ∗
   ⌜0x20000000 <= bv_unsigned sp - 32 /\
     bv_unsigned sp < 0x40000000⌝ ∗
   (bv_unsigned sp - 32) ↦ₘ? 32)%I.

Global Instance : LithiumUnfold
    (@writeSuccessSuffixOptionalU64159b8CallPrefix) := I.
