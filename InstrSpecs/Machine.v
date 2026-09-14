From Coq Require Import Lists.List.
Require Import isla.riscv64.riscv64.
Require Export ZesuMachineMap.Machine.

Import ListNotations.

Definition zesu_sys_regs : list (reg_kind * valu_shape) := [
  (KindReg "rv_enable_pmp", ExactShape (RVal_Bool (mapEnablePmp defaultMap)));
  (KindReg "rv_enable_misaligned_access", ExactShape (RVal_Bool (mapEnableMisalignedAccess defaultMap)));
  (KindReg "rv_ram_base", ExactShape (RVal_Bits (BV 64 (mapRamBase defaultMap))));
  (KindReg "rv_ram_size", ExactShape (RVal_Bits (BV 64 (mapRamSize defaultMap))));
  (KindReg "rv_rom_base", ExactShape (RVal_Bits (BV 64 (mapRomBase defaultMap))));
  (KindReg "rv_rom_size", ExactShape (RVal_Bits (BV 64 (mapRomSize defaultMap))));
  (KindReg "rv_clint_base", ExactShape (RVal_Bits (BV 64 (mapClintBase defaultMap))));
  (KindReg "rv_clint_size", ExactShape (RVal_Bits (BV 64 (mapClintSize defaultMap))));
  (KindReg "rv_htif_tohost", ExactShape (RVal_Bits (BV 64 (mapHtifTohost defaultMap))));
  (KindReg "cur_privilege", ExactShape (RVal_Enum (mapPrivilege defaultMap)));
  (KindReg "misa", ExactShape (RegVal_Struct [
    ("bits", RVal_Bits (BV 64 (mapMisa defaultMap)))]));
  (KindReg "mtvec", ExactShape (RegVal_Struct [
    ("bits", RVal_Bits (BV 64 (mapMtvec defaultMap)))]));
  (KindReg "mstatus", StructShape [("bits", MaskShape 64 (mapMstatusMask defaultMap) (mapMstatusValue defaultMap))]);
  (KindReg "satp", BitsShape 64)
].

Notation zesu_instr_sys_regs := zesu_sys_regs.
Notation zesu_ram_sys_regs := zesu_sys_regs.
