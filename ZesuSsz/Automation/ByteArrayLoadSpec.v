(* The byte-array load specification that `ArrayLoadPriority.v` recognizes
   in an instruction table. Moved here from InstrSpecs/Specs.v by P0-B
   (decision D-5): the trace generator no longer writes a `//@spec:` for an
   array load, so only automation names this specification. *)
Require Import isla.isla.
Require Import isla.riscv64.riscv64.
Require Import ZesuMachineMap.Machine.
Require Import InstrSpecs.Machine InstrSpecs.Specs.

Definition zesu_lbu_byte_array_at_spec `{!islaG Σ} `{!threadG}
    (pc : Z) (Rdst Rbase : string) (offset arrayOffset : Z)
    (index : nat) : iProp Σ :=
  ∃ (base : bv 64) (byte : bv 8) (values : list (bv 8)),
  reg_col zesu_instr_sys_regs ∗
  Rdst ↦ᵣ: (fun _ => True)%I ∗ Rbase ↦ᵣ RVal_Bits base ∗
  (bv_unsigned base + offset) ↦ₘ byte ∗
  (bv_unsigned base + arrayOffset) ↦ₘ∗ take index values ∗
  (bv_unsigned base + arrayOffset + Z.of_nat (index + 1)) ↦ₘ∗
    drop (index + 1) values ∗
  ⌜(offset = arrayOffset + Z.of_nat index)%Z⌝ ∗
  ⌜(index < length values)%nat⌝ ∗
  ⌜values !! index = Some byte⌝ ∗
  ⌜(mapRamBase defaultMap) <= bv_unsigned base + offset < (machineRamEnd defaultMap)⌝ ∗
  instr_pre (pc + 4) (
    reg_col zesu_instr_sys_regs ∗
    Rdst ↦ᵣ RVal_Bits
      (bv_zero_extend 64 byte) ∗
    Rbase ↦ᵣ RVal_Bits base ∗
    (bv_unsigned base + offset) ↦ₘ byte ∗
    (bv_unsigned base + arrayOffset) ↦ₘ∗ take index values ∗
    (bv_unsigned base + arrayOffset + Z.of_nat (index + 1)) ↦ₘ∗
      drop (index + 1) values ∗ True).

Global Instance : LithiumUnfold (@zesu_lbu_byte_array_at_spec) := I.

