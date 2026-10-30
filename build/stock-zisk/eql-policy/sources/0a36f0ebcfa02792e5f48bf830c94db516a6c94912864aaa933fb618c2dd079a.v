From Coq Require Import Strings.String Lists.List ZArith.ZArith.
From stdpp Require Import base list decidable bitvector.definitions.
Require Import isla.riscv64.riscv64.
Require Import InstrSpecs.Machine.
Open Scope string_scope.
Open Scope Z_scope.

(* Physical byte-payload spans. Platform register and zero-fill responses
   remain separate cases of the load trace. No input-end value is fixed. *)
Definition platformLoadRegion (machine : MachineMap)
    (inputEndWord pointer : bv 64%N) (size : Z) : Prop :=
  (0 <= size /\
   ((mapRamBase machine <= bv_unsigned pointer /\
     bv_unsigned pointer + size <= machineRamEnd machine) \/
    (mapInputBufferAddress machine <= bv_unsigned pointer /\
     bv_unsigned pointer + size <=
       mapInputBufferAddress machine + mapInputCapacity machine /\
     bv_unsigned pointer + size <= bv_unsigned inputEndWord) \/
    (mapRodataBase machine <= bv_unsigned pointer /\
     bv_unsigned pointer + size <= mapRodataEnd machine)))%Z.

(* Remove only the actual input-end row. All other shapes retain their order. *)
Definition platformResidualSystemRegs (machine : MachineMap) :
    list (reg_kind * valu_shape) :=
  List.filter
    (fun item => negb (bool_decide (item.1 = KindReg "zisk_input_end")))
    (machine_sys_regs machine).
