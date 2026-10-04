From Coq Require Import Lists.List.
Require Import isla.riscv64.riscv64.
Require Export ZesuMachineMap.Machine.

Import ListNotations.

Definition machine_static_sys_regs (machine : MachineMap) : list (reg_kind * valu_shape) := [
  (KindReg "rv_enable_pmp", ExactShape (RVal_Bool (mapEnablePmp machine)));
  (KindReg "rv_enable_misaligned_access", ExactShape (RVal_Bool (mapEnableMisalignedAccess machine)));
  (KindReg "rv_ram_base", ExactShape (RVal_Bits (Z_to_bv 64 (mapRamBase machine))));
  (KindReg "rv_ram_size", ExactShape (RVal_Bits (Z_to_bv 64 (mapRamSize machine))));
  (KindReg "rv_rom_base", ExactShape (RVal_Bits (Z_to_bv 64 (mapRomBase machine))));
  (KindReg "rv_rom_size", ExactShape (RVal_Bits (Z_to_bv 64 (mapRomSize machine))));
  (KindReg "rv_clint_base", ExactShape (RVal_Bits (Z_to_bv 64 (mapClintBase machine))));
  (KindReg "rv_clint_size", ExactShape (RVal_Bits (Z_to_bv 64 (mapClintSize machine))));
  (KindReg "rv_htif_tohost", ExactShape (RVal_Bits (Z_to_bv 64 (mapHtifTohost machine))));
  (KindReg "cur_privilege", ExactShape (RVal_Enum (mapPrivilege machine)));
  (KindReg "misa", ExactShape (RegVal_Struct [
    ("bits", RVal_Bits (Z_to_bv 64 (mapMisa machine)))]));
  (KindReg "mtvec", ExactShape (RegVal_Struct [
    ("bits", RVal_Bits (Z_to_bv 64 (mapMtvec machine)))]));
  (KindReg "mstatus", StructShape [("bits", MaskShape 64 (mapMstatusMask machine) (mapMstatusValue machine))]);
  (KindReg "satp", BitsShape 64)
].

Definition machine_sys_regs (machine : MachineMap) : list (reg_kind * valu_shape) :=
  machine_static_sys_regs machine ++
  if mapZiskPlatform machine then
    [(KindReg "zisk_input_end", BitsShape 64);
     (KindReg "zisk_free_input", BitsShape 64)]
  else [].

Definition zesu_sys_regs := machine_sys_regs defaultMap.

Notation zesu_instr_sys_regs := zesu_sys_regs.
Notation zesu_ram_sys_regs := zesu_sys_regs.
