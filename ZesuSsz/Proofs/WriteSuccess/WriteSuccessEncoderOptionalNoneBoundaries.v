From Coq Require Import Lists.List ZArith.ZArith.
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Contracts.IslarisMachine.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessEvents.

Definition encoderOptionalNoneFinal `{!islaG Sigma} `{!threadG}
    (data value sp ret old_x8 : bv 64) (tail : spec) (P : iProp Sigma) :
    iProp Sigma :=
  (∃ final_x6 : bv 64,
    reg_col zesu_ram_sys_regs ∗
    "x1" ↦ᵣ RVal_Bits ret ∗ "x2" ↦ᵣ RVal_Bits sp ∗
    "x5" ↦ᵣ RVal_Bits (BV 64 0x2401a0b8) ∗
    "x6" ↦ᵣ RVal_Bits final_x6 ∗ "x8" ↦ᵣ RVal_Bits old_x8 ∗
    "x10" ↦ᵣ RVal_Bits ((sp - BV 64 9)%bv) ∗
    "x11" ↦ᵣ RVal_Bits (BV 64 1) ∗
    bv_unsigned data ↦ₘ value ∗ (bv_unsigned data + 8) ↦ₘ (BV 8 0) ∗
    (bv_unsigned sp - 16) ↦ₘ? 7 ∗
    (bv_unsigned sp - 9) ↦ₘ (BV 8 0) ∗
    (bv_unsigned sp - 8) ↦ₘ ret ∗
    mmio_range 0x2401a0c0 16 ∗ spec_trace tail ∗ P ∗ True)%I.

Global Instance : LithiumUnfold (@encoderOptionalNoneFinal) := I.

Definition encoderOptionalNoneSpec `{!islaG Sigma} `{!threadG}
    (data value sp ret : bv 64) (tail : spec) (P : iProp Sigma) : iProp Sigma :=
  (∃ (old_x5 old_x6 old_x8 old_x11 stackByte stackRa : bv 64),
    reg_col zesu_ram_sys_regs ∗
    "x1" ↦ᵣ RVal_Bits ret ∗ "x2" ↦ᵣ RVal_Bits sp ∗
    "x5" ↦ᵣ RVal_Bits old_x5 ∗ "x6" ↦ᵣ RVal_Bits old_x6 ∗
    "x8" ↦ᵣ RVal_Bits old_x8 ∗
    "x10" ↦ᵣ RVal_Bits data ∗ "x11" ↦ᵣ RVal_Bits old_x11 ∗
    bv_unsigned data ↦ₘ value ∗
    (bv_unsigned data + 8) ↦ₘ (BV 8 0) ∗
    (bv_unsigned sp - 16) ↦ₘ? 7 ∗
    (bv_unsigned sp - 9) ↦ₘ (bv_extract 0 8 stackByte) ∗
    (bv_unsigned sp - 8) ↦ₘ stackRa ∗
    mmio_range 0x2401a0c0 16 ∗
    spec_trace
      (writeOutputEvents ((sp - BV 64 9)%bv) (BV 64 1) tail) ∗
    ⌜bv_extract 0 3 data = BV 3 0⌝ ∗
    ⌜(0x20000000 <= bv_unsigned data)%Z⌝ ∗
    ⌜(bv_unsigned data + 8 < 0x40000000)%Z⌝ ∗
    ⌜bv_extract 0 4 sp = BV 4 0⌝ ∗
    ⌜bv_extract 0 3 sp = BV 3 0⌝ ∗
    ⌜(0x20000000 <= bv_unsigned sp - 16)%Z⌝ ∗
    ⌜(bv_unsigned sp < 0x40000000)%Z⌝ ∗
    ⌜bv_extract 0 1 ret = BV 1 0⌝ ∗
    ⌜bv_extract 1 1 ret = BV 1 0⌝ ∗
    ⌜bv_extract 0 2 ret = BV 2 0⌝ ∗ P ∗
    instr_pre (bv_unsigned ret)
      (encoderOptionalNoneFinal data value sp ret old_x8 tail P) ∗ True)%I.

Global Instance : LithiumUnfold (@encoderOptionalNoneSpec) := I.

Definition encoderOptionalNoneAtTail `{!islaG Sigma} `{!threadG}
    (data value sp ret : bv 64) (tail : spec) (P : iProp Sigma) : iProp Sigma :=
  (∃ (old_x5 old_x6 old_x8 stackByte stackRa : bv 64),
    reg_col zesu_ram_sys_regs ∗
    "x1" ↦ᵣ RVal_Bits ret ∗ "x2" ↦ᵣ RVal_Bits sp ∗
    "x5" ↦ᵣ RVal_Bits old_x5 ∗ "x6" ↦ᵣ RVal_Bits old_x6 ∗
    "x8" ↦ᵣ RVal_Bits old_x8 ∗
    "x10" ↦ᵣ RVal_Bits data ∗ "x11" ↦ᵣ RVal_Bits (BV 64 0) ∗
    bv_unsigned data ↦ₘ value ∗
    (bv_unsigned data + 8) ↦ₘ (BV 8 0) ∗
    (bv_unsigned sp - 16) ↦ₘ? 7 ∗
    (bv_unsigned sp - 9) ↦ₘ (bv_extract 0 8 stackByte) ∗
    (bv_unsigned sp - 8) ↦ₘ stackRa ∗
    mmio_range 0x2401a0c0 16 ∗
    spec_trace
      (writeOutputEvents ((sp - BV 64 9)%bv) (BV 64 1) tail) ∗
    ⌜bv_extract 0 3 data = BV 3 0⌝ ∗
    ⌜(0x20000000 <= bv_unsigned data)%Z⌝ ∗
    ⌜(bv_unsigned data + 8 < 0x40000000)%Z⌝ ∗
    ⌜bv_extract 0 4 sp = BV 4 0⌝ ∗
    ⌜bv_extract 0 3 sp = BV 3 0⌝ ∗
    ⌜(0x20000000 <= bv_unsigned sp - 16)%Z⌝ ∗
    ⌜(bv_unsigned sp < 0x40000000)%Z⌝ ∗
    ⌜bv_extract 0 1 ret = BV 1 0⌝ ∗
    ⌜bv_extract 1 1 ret = BV 1 0⌝ ∗
    ⌜bv_extract 0 2 ret = BV 2 0⌝ ∗ P ∗
    instr_pre (bv_unsigned ret)
      (encoderOptionalNoneFinal data value sp ret old_x8 tail P) ∗ True)%I.

Global Instance : LithiumUnfold (@encoderOptionalNoneAtTail) := I.

Definition encoderOptionalNoneAtBoolean `{!islaG Sigma} `{!threadG}
    (data value sp ret : bv 64) (tail : spec) (P : iProp Sigma) : iProp Sigma :=
  (∃ (old_x5 old_x6 old_x8 stackByte stackRa : bv 64),
    reg_col zesu_ram_sys_regs ∗
    "x1" ↦ᵣ RVal_Bits ret ∗ "x2" ↦ᵣ RVal_Bits sp ∗
    "x5" ↦ᵣ RVal_Bits old_x5 ∗ "x6" ↦ᵣ RVal_Bits old_x6 ∗
    "x8" ↦ᵣ RVal_Bits old_x8 ∗
    "x10" ↦ᵣ RVal_Bits (BV 64 0) ∗ "x11" ↦ᵣ RVal_Bits (BV 64 0) ∗
    bv_unsigned data ↦ₘ value ∗
    (bv_unsigned data + 8) ↦ₘ (BV 8 0) ∗
    (bv_unsigned sp - 16) ↦ₘ? 7 ∗
    (bv_unsigned sp - 9) ↦ₘ (bv_extract 0 8 stackByte) ∗
    (bv_unsigned sp - 8) ↦ₘ stackRa ∗
    mmio_range 0x2401a0c0 16 ∗
    spec_trace
      (writeOutputEvents ((sp - BV 64 9)%bv) (BV 64 1) tail) ∗
    ⌜bv_extract 0 3 data = BV 3 0⌝ ∗
    ⌜(0x20000000 <= bv_unsigned data)%Z⌝ ∗
    ⌜(bv_unsigned data + 8 < 0x40000000)%Z⌝ ∗
    ⌜bv_extract 0 4 sp = BV 4 0⌝ ∗
    ⌜bv_extract 0 3 sp = BV 3 0⌝ ∗
    ⌜(0x20000000 <= bv_unsigned sp - 16)%Z⌝ ∗
    ⌜(bv_unsigned sp < 0x40000000)%Z⌝ ∗
    ⌜bv_extract 0 1 ret = BV 1 0⌝ ∗
    ⌜bv_extract 1 1 ret = BV 1 0⌝ ∗
    ⌜bv_extract 0 2 ret = BV 2 0⌝ ∗ P ∗
    instr_pre (bv_unsigned ret)
      (encoderOptionalNoneFinal data value sp ret old_x8 tail P) ∗ True)%I.

Global Instance : LithiumUnfold (@encoderOptionalNoneAtBoolean) := I.
