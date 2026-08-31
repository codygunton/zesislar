From Coq Require Import Lists.List.
Require Import isla.riscv64.riscv64.

Import ListNotations.

Definition zesu_sys_regs : list (reg_kind * valu_shape) := [
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
  (KindReg "mtvec", ExactShape (RegVal_Struct [
    ("bits", RVal_Bits (BV 64 0))]));
  (KindReg "mstatus", StructShape [("bits", MaskShape 64 0x20000 0)]);
  (KindReg "satp", BitsShape 64)
].

Notation zesu_instr_sys_regs := zesu_sys_regs.
Notation zesu_ram_sys_regs := zesu_sys_regs.
