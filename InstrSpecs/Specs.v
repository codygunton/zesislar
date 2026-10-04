(** Reusable instruction specifications.
Require Import ZesuMachineMap.Machine.

    Each spec describes what one instruction does in terms of separation-logic
    resources — no Isla trace in sight. Mark each with [LithiumUnfold] so the
    proof search can look inside it. The dump invokes them via [//@spec:] and
    [//@import:] annotations.

    Start with the most common instructions and grow the library as you
    encounter new opcodes in the binary. *)
Require Import isla.isla.
Require Import isla.riscv64.riscv64.
Require Export InstrSpecs.Machine.

Import ListNotations.


Definition rv64_sd_spec `{!islaG Σ} `{!threadG}
    (system_regs : list (reg_kind * valu_shape)) (ram_start ram_end pc : Z)
    (Rsrc Rbase : string) (offset : Z) : iProp Σ :=
  ∃ (src base : bv 64),
  reg_col system_regs ∗
  Rsrc ↦ᵣ RVal_Bits src ∗ Rbase ↦ᵣ RVal_Bits base ∗
  (bv_unsigned base + offset) ↦ₘ? 8 ∗
  ⌜bv_unsigned base `mod` 8 = 0⌝ ∗
  ⌜ram_start <= bv_unsigned base + offset ∧
    bv_unsigned base + offset + 8 <= ram_end⌝ ∗
  instr_pre (pc + 4) (
    reg_col system_regs ∗
    Rsrc ↦ᵣ RVal_Bits src ∗ Rbase ↦ᵣ RVal_Bits base ∗
    (bv_unsigned base + offset) ↦ₘ src ∗ True).

Global Instance : LithiumUnfold (@rv64_sd_spec) := I.

Definition machine_sd_spec `{!islaG Σ} `{!threadG} (machine : MachineMap) :=
  @rv64_sd_spec Σ _ _ (machine_sys_regs machine) (mapRamBase machine) (machineRamEnd machine).

Global Instance : LithiumUnfold (@machine_sd_spec) := I.

Definition zesu_sd_spec `{!islaG Σ} `{!threadG} :=
  @machine_sd_spec Σ _ _ defaultMap.
Global Instance : LithiumUnfold (@zesu_sd_spec) := I.

Definition rv64_ld_spec `{!islaG Σ} `{!threadG}
    (system_regs : list (reg_kind * valu_shape)) (ram_start ram_end pc : Z)
    (Rdst Rbase : string) (offset : Z) : iProp Σ :=
  ∃ (value base : bv 64),
  reg_col system_regs ∗
  Rdst ↦ᵣ: (fun _ => True)%I ∗ Rbase ↦ᵣ RVal_Bits base ∗
  (bv_unsigned base + offset) ↦ₘ value ∗
  ⌜bv_unsigned base `mod` 8 = 0⌝ ∗
  ⌜ram_start <= bv_unsigned base + offset ∧
    bv_unsigned base + offset + 8 <= ram_end⌝ ∗
  instr_pre (pc + 4) (
    reg_col system_regs ∗
    Rdst ↦ᵣ RVal_Bits value ∗ Rbase ↦ᵣ RVal_Bits base ∗
    (bv_unsigned base + offset) ↦ₘ value ∗ True).

Global Instance : LithiumUnfold (@rv64_ld_spec) := I.

Definition machine_ld_spec `{!islaG Σ} `{!threadG} (machine : MachineMap) :=
  @rv64_ld_spec Σ _ _ (machine_sys_regs machine) (mapRamBase machine) (machineRamEnd machine).

Global Instance : LithiumUnfold (@machine_ld_spec) := I.

Definition zesu_ld_spec `{!islaG Σ} `{!threadG} :=
  @machine_ld_spec Σ _ _ defaultMap.
Global Instance : LithiumUnfold (@zesu_ld_spec) := I.

Definition machine_ld_array_spec `{!islaG Σ} `{!threadG}
    (machine : MachineMap)
    (pc : Z) (Rdst Rbase : string) (offset : Z) : iProp Σ :=
  ∃ (value base : bv 64) (arrayBase : Z) (values : list (bv 64))
      (index : nat),
  reg_col (machine_sys_regs machine) ∗
  Rdst ↦ᵣ: (fun _ => True)%I ∗ Rbase ↦ᵣ RVal_Bits base ∗
  arrayBase ↦ₘ∗ values ∗
  ⌜(bv_unsigned base + offset = arrayBase + 8 * Z.of_nat index)%Z⌝ ∗
  ⌜values !! index = Some value⌝ ∗
  ⌜bv_unsigned base `mod` 8 = 0⌝ ∗
  ⌜mapRamBase machine <= bv_unsigned base + offset ∧
    bv_unsigned base + offset + 8 <= machineRamEnd machine⌝ ∗
  instr_pre (pc + 4) (
    reg_col (machine_sys_regs machine) ∗
    Rdst ↦ᵣ RVal_Bits value ∗ Rbase ↦ᵣ RVal_Bits base ∗
    arrayBase ↦ₘ∗ values ∗ True).

Global Instance : LithiumUnfold (@machine_ld_array_spec) := I.

Definition zesu_ld_array_spec `{!islaG Σ} `{!threadG} :=
  @machine_ld_array_spec Σ _ _ defaultMap.
Global Instance : LithiumUnfold (@zesu_ld_array_spec) := I.

Definition machine_ld_same_byte_array_at_spec `{!islaG Σ} `{!threadG}
    (machine : MachineMap)
    (pc : Z) (R : string) (offset arrayOffset : Z)
    (index : nat) : iProp Σ :=
  ∃ (base word : bv 64) (values : list (bv 8)),
  reg_col (machine_sys_regs machine) ∗
  R ↦ᵣ RVal_Bits base ∗
  (bv_unsigned base + offset) ↦ₘ word ∗
  (bv_unsigned base + arrayOffset) ↦ₘ∗ take index values ∗
  (bv_unsigned base + arrayOffset + Z.of_nat (index + 8)) ↦ₘ∗
    drop (index + 8) values ∗
  ⌜(offset = arrayOffset + Z.of_nat index)%Z⌝ ∗
  ⌜(index + 8 <= length values)%nat⌝ ∗
  ⌜word = Z_to_bv 64
    (little_endian_to_bv 8 (take 8 (drop index values)))⌝ ∗
  ⌜bv_unsigned base `mod` 8 = 0⌝ ∗
  ⌜mapRamBase machine <= bv_unsigned base + offset ∧
    bv_unsigned base + offset + 8 <= machineRamEnd machine⌝ ∗
  instr_pre (pc + 4) (
    reg_col (machine_sys_regs machine) ∗
    R ↦ᵣ RVal_Bits
      word ∗
    (bv_unsigned base + offset) ↦ₘ word ∗
    (bv_unsigned base + arrayOffset) ↦ₘ∗ take index values ∗
    (bv_unsigned base + arrayOffset + Z.of_nat (index + 8)) ↦ₘ∗
      drop (index + 8) values ∗ True).

Global Instance : LithiumUnfold (@machine_ld_same_byte_array_at_spec) := I.

Definition zesu_ld_same_byte_array_at_spec `{!islaG Σ} `{!threadG} :=
  @machine_ld_same_byte_array_at_spec Σ _ _ defaultMap.
Global Instance : LithiumUnfold (@zesu_ld_same_byte_array_at_spec) := I.

Ltac solve_zesu_ld_array :=
  multimatch goal with
  | Hactual : ?values !! ?actual = Some ?loaded
    |- bv_sign_extend 64 ?loaded = ?value =>
    lazymatch actual with
    | Z.to_nat ((bv_unsigned (?base + ?offsetBv) - ?arrayBase) `div` 8) =>
    multimatch goal with
    | Hexpected : values !! ?index = Some value |- _ =>
    match goal with
    | Haddress : (bv_unsigned base + ?offset =
        arrayBase + 8 * ?indexZ)%Z |- _ =>
      let Hbaseadd := fresh "Hbaseadd" in
      assert (Hbaseadd :
        bv_unsigned (base + offsetBv) = bv_unsigned base + offset) by
        bv_solve;
      let Hindex := fresh "Hindex" in
      assert (Hindex :
        Z.to_nat ((bv_unsigned (base + offsetBv) - arrayBase) `div` 8) =
          index) by
         (rewrite Hbaseadd Haddress;
         replace (arrayBase + 8 * indexZ - arrayBase)%Z with
           (indexZ * 8)%Z by ring;
         try rewrite Z.div_mul; lia);
      rewrite Hindex in Hactual;
      rewrite Hexpected in Hactual;
      injection Hactual as ->;
      bv_solve
    end
    end
    end
  end.

Ltac solve_zesu_ld_array_with Haddress Hexpected Hactual :=
  lazymatch type of Hactual with
  | ?values !! Z.to_nat
      ((bv_unsigned (?base + ?offsetBv) - ?arrayBase) `div` 8) =
      Some ?loaded =>
    lazymatch type of Hexpected with
    | values !! ?index = Some ?value =>
      lazymatch type of Haddress with
      | (bv_unsigned base + ?offset = arrayBase + 8 * ?indexZ)%Z =>
        let Hbaseadd := fresh "Hbaseadd" in
        assert (Hbaseadd :
          bv_unsigned (base + offsetBv) = bv_unsigned base + offset) by
          bv_solve;
        let Hindex := fresh "Hindex" in
        assert (Hindex :
          Z.to_nat ((bv_unsigned (base + offsetBv) - arrayBase) `div` 8) =
            index) by
          (rewrite Hbaseadd Haddress;
           replace (arrayBase + 8 * indexZ - arrayBase)%Z with
             (indexZ * 8)%Z by ring;
           try rewrite Z.div_mul; lia);
        rewrite Hindex in Hactual;
        rewrite Hexpected in Hactual;
        injection Hactual as ->;
        bv_solve
      end
    end
  end.

Definition machine_ld_same_spec `{!islaG Σ} `{!threadG}
    (machine : MachineMap)
    (pc : Z) (R : string) (offset : Z) : iProp Σ :=
  ∃ (value base : bv 64),
  reg_col (machine_sys_regs machine) ∗
  R ↦ᵣ RVal_Bits base ∗ (bv_unsigned base + offset) ↦ₘ value ∗
  ⌜bv_unsigned base `mod` 8 = 0⌝ ∗
  ⌜mapRamBase machine <= bv_unsigned base + offset ∧
    bv_unsigned base + offset + 8 <= machineRamEnd machine⌝ ∗
  instr_pre (pc + 4) (
    reg_col (machine_sys_regs machine) ∗
    R ↦ᵣ RVal_Bits value ∗ (bv_unsigned base + offset) ↦ₘ value ∗ True).

Global Instance : LithiumUnfold (@machine_ld_same_spec) := I.

Definition zesu_ld_same_spec `{!islaG Σ} `{!threadG} :=
  @machine_ld_same_spec Σ _ _ defaultMap.
Global Instance : LithiumUnfold (@zesu_ld_same_spec) := I.

Definition machine_jalr_same_spec `{!islaG Σ} `{!threadG}
    (machine : MachineMap)
    (pc : Z) (R : string) (offset : bv 64) : iProp Σ :=
  ∃ base : bv 64,
  reg_col (machine_sys_regs machine) ∗ R ↦ᵣ RVal_Bits base ∗
  ⌜bv_extract 0 2 (base + offset) = BV 2 0⌝ ∗
  instr_pre
    (bv_unsigned
      (bv_or (bv_and (base + offset)
        (BV 64 18446744073709551614)) (BV 64 0))) (
    reg_col (machine_sys_regs machine) ∗
    R ↦ᵣ RVal_Bits (Z_to_bv 64 (pc + 4)) ∗ True).

Global Instance : LithiumUnfold (@machine_jalr_same_spec) := I.

Definition zesu_jalr_same_spec `{!islaG Σ} `{!threadG} :=
  @machine_jalr_same_spec Σ _ _ defaultMap.
Global Instance : LithiumUnfold (@zesu_jalr_same_spec) := I.

Definition machine_move_x9_x10_spec `{!islaG Σ} `{!threadG}
    (machine : MachineMap) (pc : Z) : iProp Σ :=
  ∃ src : bv 64,
  reg_col (machine_sys_regs machine) ∗
  "x9" ↦ᵣ RVal_Bits src ∗
  "x10" ↦ᵣ: (fun _ => True)%I ∗
  instr_pre (pc + 4) (
    reg_col (machine_sys_regs machine) ∗
    "x9" ↦ᵣ RVal_Bits src ∗
    "x10" ↦ᵣ RVal_Bits src ∗ True).
Global Instance : LithiumUnfold (@machine_move_x9_x10_spec) := I.

Definition machine_auipc_zero_x1_spec `{!islaG Σ} `{!threadG}
    (machine : MachineMap) (pc : Z) : iProp Σ :=
  reg_col (machine_sys_regs machine) ∗
  "x1" ↦ᵣ: (fun _ => True)%I ∗
  instr_pre (pc + 4) (
    reg_col (machine_sys_regs machine) ∗
    "x1" ↦ᵣ RVal_Bits (Z_to_bv 64 pc) ∗ True).
Global Instance : LithiumUnfold (@machine_auipc_zero_x1_spec) := I.
