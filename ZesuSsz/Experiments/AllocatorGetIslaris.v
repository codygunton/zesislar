Require Import isla.riscv64.riscv64.
From IslaTraces.allocator_get Require Import instrs.

Definition allocator_sys_regs : list (reg_kind * valu_shape) := [
  (KindReg "rv_enable_pmp", ExactShape (RVal_Bool false));
  (KindReg "rv_enable_misaligned_access", ExactShape (RVal_Bool false));
  (KindReg "rv_ram_base", ExactShape (RVal_Bits (BV 64 0x20000000)));
  (KindReg "rv_ram_size", ExactShape (RVal_Bits (BV 64 0x20000000)));
  (KindReg "rv_rom_base", ExactShape (RVal_Bits (BV 64 0x1000)));
  (KindReg "rv_rom_size", ExactShape (RVal_Bits (BV 64 0x100)));
  (KindReg "rv_clint_base", ExactShape (RVal_Bits (BV 64 0x2000000)));
  (KindReg "rv_clint_size", ExactShape (RVal_Bits (BV 64 0xc0000)));
  (KindReg "rv_htif_tohost", ExactShape (RVal_Bits (BV 64 0x40001000)));
  (KindReg "cur_privilege", ExactShape (RVal_Enum "Machine"));
  (KindReg "misa", ExactShape (RegVal_Struct [
    ("bits", RVal_Bits (BV 64 0x8000000000001100))]));
  (KindReg "mstatus", StructShape [("bits", MaskShape 64 0x20000 0)]);
  (KindReg "satp", BitsShape 64)
].

Lemma allocator_get_instruction_body `{!islaG Σ} `{!threadG}
    (sp old_x10 old_x11 old_x12 old_x13 stack0 stack8 : bv 64) :
  instr 0x14ccc (Some a14ccc) -∗
  instr 0x14cd0 (Some a14cd0) -∗
  instr 0x14cd4 (Some a14cd4) -∗
  instr 0x14cd8 (Some a14cd8) -∗
  instr 0x14cdc (Some a14cdc) -∗
  instr 0x14ce0 (Some a14ce0) -∗
  instr 0x14ce4 (Some a14ce4) -∗
  instr 0x14ce8 (Some a14ce8) -∗
  instr_body 0x14ccc (
    reg_col allocator_sys_regs ∗
    "x2" ↦ᵣ RVal_Bits sp ∗
    "x10" ↦ᵣ RVal_Bits old_x10 ∗
    "x11" ↦ᵣ RVal_Bits old_x11 ∗
    "x12" ↦ᵣ RVal_Bits old_x12 ∗
    "x13" ↦ᵣ RVal_Bits old_x13 ∗
    bv_unsigned sp ↦ₘ stack0 ∗
    (bv_unsigned sp + 8) ↦ₘ stack8 ∗
    (bv_unsigned sp + 16) ↦ₘ? 8 ∗
    (bv_unsigned sp + 24) ↦ₘ? 8 ∗
    ⌜bv_unsigned sp `mod` 8 = 0⌝ ∗
    ⌜0x20000000 ≤ bv_unsigned sp⌝ ∗
    ⌜bv_unsigned sp + 24 < 0x40000000⌝ ∗
    instr_pre 0x14cec (
      reg_col allocator_sys_regs ∗
      "x2" ↦ᵣ RVal_Bits sp ∗
      "x10" ↦ᵣ RVal_Bits (BV 64 0x2401a0b0) ∗
      "x11" ↦ᵣ RVal_Bits (BV 64 0x177a8) ∗
      "x12" ↦ᵣ RVal_Bits stack0 ∗
      "x13" ↦ᵣ RVal_Bits stack8 ∗
      bv_unsigned sp ↦ₘ stack0 ∗
      (bv_unsigned sp + 8) ↦ₘ stack8 ∗
      (bv_unsigned sp + 16) ↦ₘ (BV 64 0x2401a0b0) ∗
      (bv_unsigned sp + 24) ↦ₘ (BV 64 0x177a8) ∗
      True)).
Proof.
  iStartProof.
  repeat liAStep; liShow.
  Unshelve. all: prepare_sidecond.
  all: try bv_solve.
Qed.
