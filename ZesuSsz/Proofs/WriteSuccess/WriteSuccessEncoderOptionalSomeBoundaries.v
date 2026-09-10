From Coq Require Import Lists.List ZArith.ZArith.
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Contracts.IslarisMachine.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessEvents.

Definition encoderOptionalSomeFinal `{!islaG Sigma} `{!threadG}
    (data value sp ret : bv 64) (tag : bv 8) (old_x8 : bv 64)
    (tail : spec) (P : iProp Sigma) : iProp Sigma :=
  (∃ final_x6 : bv 64,
    reg_col zesu_ram_sys_regs ∗
    "x1" ↦ᵣ RVal_Bits ret ∗ "x2" ↦ᵣ RVal_Bits sp ∗
    "x5" ↦ᵣ RVal_Bits (BV 64 0x2401a0b8) ∗
    "x6" ↦ᵣ RVal_Bits final_x6 ∗ "x8" ↦ᵣ RVal_Bits old_x8 ∗
    "x10" ↦ᵣ RVal_Bits ((sp - BV 64 16)%bv) ∗
    "x11" ↦ᵣ RVal_Bits (BV 64 8) ∗
    bv_unsigned data ↦ₘ value ∗ (bv_unsigned data + 8) ↦ₘ tag ∗
    (bv_unsigned sp - 32) ↦ₘ? 8 ∗
    (bv_unsigned sp - 24) ↦ₘ? 8 ∗
    (bv_unsigned sp - 16) ↦ₘ? 8 ∗
    (bv_unsigned sp - 8) ↦ₘ? 8 ∗
    mmio_range 0x2401a0c0 16 ∗ spec_trace tail ∗ P ∗ True)%I.

Global Instance : LithiumUnfold (@encoderOptionalSomeFinal) := I.

Definition encoderOptionalSomeContext `{!islaG Sigma} `{!threadG}
    (data value sp ret : bv 64) (tag : bv 8) (old_x8 : bv 64)
    (events tail : spec) (P : iProp Sigma) : iProp Sigma :=
  (bv_unsigned data ↦ₘ value ∗ (bv_unsigned data + 8) ↦ₘ tag ∗
   mmio_range 0x2401a0c0 16 ∗ spec_trace events ∗
   ⌜tag ≠ BV 8 0⌝ ∗
   ⌜bv_extract 0 3 data = BV 3 0⌝ ∗
   ⌜(0x20000000 <= bv_unsigned data)%Z⌝ ∗
   ⌜(bv_unsigned data + 8 < 0x40000000)%Z⌝ ∗
   ⌜bv_extract 0 4 sp = BV 4 0⌝ ∗
   ⌜bv_extract 0 3 sp = BV 3 0⌝ ∗
   ⌜(0x20000000 <= bv_unsigned sp - 32)%Z⌝ ∗
   ⌜(bv_unsigned sp < 0x40000000)%Z⌝ ∗
   ⌜bv_extract 0 1 ret = BV 1 0⌝ ∗
   ⌜bv_extract 1 1 ret = BV 1 0⌝ ∗
   ⌜bv_extract 0 2 ret = BV 2 0⌝ ∗ P ∗
   instr_pre (bv_unsigned ret)
     (encoderOptionalSomeFinal data value sp ret tag old_x8 tail P) ∗ True)%I.

Global Instance : LithiumUnfold (@encoderOptionalSomeContext) := I.

Definition encoderOptionalSomeInitialEvents
    (sp : bv 64) (tail : spec) : spec :=
  writeOutputEvents ((sp - BV 64 16 - BV 64 16 + BV 64 7)%bv)
    (BV 64 1)
    (writeOutputEvents ((sp - BV 64 16)%bv) (BV 64 8) tail).

Definition encoderOptionalSomeAfterBooleanEvents
    (sp : bv 64) (tail : spec) : spec :=
  writeOutputEvents ((sp - BV 64 16)%bv) (BV 64 8) tail.

Definition encoderOptionalSomeSpec `{!islaG Sigma} `{!threadG}
    (data value sp ret : bv 64) (tag : bv 8)
    (tail : spec) (P : iProp Sigma) : iProp Sigma :=
  (∃ (old_x5 old_x6 old_x8 old_x11 : bv 64),
    reg_col zesu_ram_sys_regs ∗
    "x1" ↦ᵣ RVal_Bits ret ∗ "x2" ↦ᵣ RVal_Bits sp ∗
    "x5" ↦ᵣ RVal_Bits old_x5 ∗ "x6" ↦ᵣ RVal_Bits old_x6 ∗
    "x8" ↦ᵣ RVal_Bits old_x8 ∗
    "x10" ↦ᵣ RVal_Bits data ∗ "x11" ↦ᵣ RVal_Bits old_x11 ∗
    (bv_unsigned sp - 32) ↦ₘ? 32 ∗
    encoderOptionalSomeContext data value sp ret tag old_x8
      (encoderOptionalSomeInitialEvents sp tail) tail P ∗ True)%I.

Global Instance : LithiumUnfold (@encoderOptionalSomeSpec) := I.

Definition encoderOptionalSomeAtSomeBody `{!islaG Sigma} `{!threadG}
    (data value sp ret : bv 64) (tag : bv 8)
    (tail : spec) (P : iProp Sigma) : iProp Sigma :=
  (∃ old_x5 old_x6 old_x8 : bv 64,
    reg_col zesu_ram_sys_regs ∗
    "x1" ↦ᵣ RVal_Bits ret ∗ "x2" ↦ᵣ RVal_Bits sp ∗
    "x5" ↦ᵣ RVal_Bits old_x5 ∗ "x6" ↦ᵣ RVal_Bits old_x6 ∗
    "x8" ↦ᵣ RVal_Bits old_x8 ∗
    "x10" ↦ᵣ RVal_Bits data ∗
    "x11" ↦ᵣ RVal_Bits (bv_zero_extend 64 tag) ∗
    (bv_unsigned sp - 32) ↦ₘ? 32 ∗
    encoderOptionalSomeContext data value sp ret tag old_x8
      (encoderOptionalSomeInitialEvents sp tail) tail P ∗ True)%I.

Global Instance : LithiumUnfold (@encoderOptionalSomeAtSomeBody) := I.

Definition encoderOptionalSomeAtBranch `{!islaG Sigma} `{!threadG}
    (data value sp ret : bv 64) (tag : bv 8)
    (tail : spec) (P : iProp Sigma) : iProp Sigma :=
  (∃ old_x5 old_x6 old_x8 : bv 64,
    reg_col zesu_ram_sys_regs ∗
    "x1" ↦ᵣ RVal_Bits ret ∗ "x2" ↦ᵣ RVal_Bits sp ∗
    "x5" ↦ᵣ RVal_Bits old_x5 ∗ "x6" ↦ᵣ RVal_Bits old_x6 ∗
    "x8" ↦ᵣ RVal_Bits old_x8 ∗
    "x10" ↦ᵣ RVal_Bits data ∗
    "x11" ↦ᵣ RVal_Bits (bv_zero_extend 64 tag) ∗
    ⌜bv_zero_extend 64 tag ≠ BV 64 0⌝ ∗
    (bv_unsigned sp - 32) ↦ₘ? 32 ∗
    encoderOptionalSomeContext data value sp ret tag old_x8
      (encoderOptionalSomeInitialEvents sp tail) tail P ∗ True)%I.

Global Instance : LithiumUnfold (@encoderOptionalSomeAtBranch) := I.

Definition encoderOptionalSomeAtBoolean `{!islaG Sigma} `{!threadG}
    (data value sp ret : bv 64) (tag : bv 8)
    (tail : spec) (P : iProp Sigma) : iProp Sigma :=
  (∃ old_x5 old_x6 old_x8 : bv 64,
    reg_col zesu_ram_sys_regs ∗
    "x1" ↦ᵣ RVal_Bits (BV 64 0x15bec) ∗
    "x2" ↦ᵣ RVal_Bits (sp - BV 64 16)%bv ∗
    "x5" ↦ᵣ RVal_Bits old_x5 ∗ "x6" ↦ᵣ RVal_Bits old_x6 ∗
    "x8" ↦ᵣ RVal_Bits value ∗ "x10" ↦ᵣ RVal_Bits (BV 64 1) ∗
    "x11" ↦ᵣ RVal_Bits (bv_zero_extend 64 tag) ∗
    (bv_unsigned sp - 32) ↦ₘ? 16 ∗
    (bv_unsigned sp - 16) ↦ₘ old_x8 ∗
    (bv_unsigned sp - 8) ↦ₘ ret ∗
    encoderOptionalSomeContext data value sp ret tag old_x8
      (encoderOptionalSomeInitialEvents sp tail) tail P ∗ True)%I.

Global Instance : LithiumUnfold (@encoderOptionalSomeAtBoolean) := I.

Definition encoderOptionalSomeAtResume `{!islaG Sigma} `{!threadG}
    (data value sp ret : bv 64) (tag : bv 8)
    (tail : spec) (P : iProp Sigma) : iProp Sigma :=
  (∃ old_x6 old_x8 : bv 64,
    reg_col zesu_ram_sys_regs ∗
    "x1" ↦ᵣ RVal_Bits (BV 64 0x15bec) ∗
    "x2" ↦ᵣ RVal_Bits (sp - BV 64 16)%bv ∗
    "x5" ↦ᵣ RVal_Bits (BV 64 0x2401a0b8) ∗
    "x6" ↦ᵣ RVal_Bits old_x6 ∗ "x8" ↦ᵣ RVal_Bits value ∗
    "x10" ↦ᵣ RVal_Bits ((sp - BV 64 25)%bv) ∗
    "x11" ↦ᵣ RVal_Bits (BV 64 1) ∗
    (bv_unsigned sp - 32) ↦ₘ? 7 ∗
    (bv_unsigned sp - 25) ↦ₘ (BV 8 1) ∗
    (bv_unsigned sp - 24) ↦ₘ (BV 64 0x15bec) ∗
    (bv_unsigned sp - 16) ↦ₘ old_x8 ∗
    (bv_unsigned sp - 8) ↦ₘ ret ∗
    encoderOptionalSomeContext data value sp ret tag old_x8
      (encoderOptionalSomeAfterBooleanEvents sp tail) tail P ∗ True)%I.

Global Instance : LithiumUnfold (@encoderOptionalSomeAtResume) := I.

Definition encoderOptionalSomeAtInt `{!islaG Sigma} `{!threadG}
    (data value sp ret : bv 64) (tag : bv 8)
    (tail : spec) (P : iProp Sigma) : iProp Sigma :=
  (∃ old_x8 : bv 64,
    reg_col zesu_ram_sys_regs ∗
    "x1" ↦ᵣ RVal_Bits ret ∗ "x2" ↦ᵣ RVal_Bits sp ∗
    "x5" ↦ᵣ RVal_Bits (BV 64 0x2401a0b8) ∗
    "x6" ↦ᵣ RVal_Bits (BV 64 0x15bfc) ∗
    "x8" ↦ᵣ RVal_Bits old_x8 ∗ "x10" ↦ᵣ RVal_Bits value ∗
    "x11" ↦ᵣ RVal_Bits (BV 64 1) ∗
    (bv_unsigned sp - 32) ↦ₘ? 32 ∗
    encoderOptionalSomeContext data value sp ret tag old_x8
      (encoderOptionalSomeAfterBooleanEvents sp tail) tail P ∗ True)%I.

Global Instance : LithiumUnfold (@encoderOptionalSomeAtInt) := I.
