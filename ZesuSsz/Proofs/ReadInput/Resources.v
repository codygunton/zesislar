Require Import ZesuSsz.Automation.All.
Require Import ZesuMachineMap.Machine.
From Coq Require Import Lists.List ZArith.ZArith.
Require Import isla.riscv64.riscv64.
From IslaTraces.read_input Require Import instrs.
Require Import ZesuSsz.Contracts.IslarisMachine.
Require Import ZesuSsz.Generated.Level1.
Require Import ZesuSsz.Contracts.Endpoints.

Import ListNotations.

Definition readInputMemory (bytes : ByteString) : list (bv 8) :=
  List.map (Z_to_bv 8) bytes.

Definition readInputIoPointer : bv 64 :=
  (Z_to_bv 64 65868 + (BV 64 604020736) +
   (BV 64 18446744073709551468))%bv.

Lemma read_input_buffer_pointer_eq :
  (Z_to_bv 64 65856 + (BV 64 536911872) +
   (BV 64 18446744073709551296))%bv = BV 64 (mapInputBufferAddress defaultMap).
Proof. apply bv_eq. vm_compute. reflexivity. Qed.

Lemma read_input_io_pointer_eq :
  readInputIoPointer = BV 64 (mapIoContextAddress defaultMap).
Proof. apply bv_eq. vm_compute. reflexivity. Qed.

#[local] Hint Rewrite read_input_buffer_pointer_eq
  : isla_coq_rewrite.

Definition read_input_resources `{!islaG Sigma} `{!threadG} :
    IslarisContractResources ReadInputArgs ReadInputOutcome := {|
  islarisCode :=
    (instr 0x10140 (Some a10140) ∗ instr 0x10144 (Some a10144) ∗
     instr 0x10148 (Some a10148) ∗ instr 0x1014c (Some a1014c) ∗
     instr 0x10150 (Some a10150) ∗ instr 0x10154 (Some a10154) ∗
     instr 0x10158 (Some a10158) ∗ instr 0x1015c (Some a1015c))%I;
  islarisEntry := fun args =>
    (∃ (bufferSlot sizeSlot sizeWord old_x5 old_x6
         oldBufferSlot oldSizeSlot savedWord : bv 64),
      ⌜bv_unsigned bufferSlot = readBufferSlot args⌝ ∗
      ⌜bv_unsigned sizeSlot = readSizeSlot args⌝ ∗
      ⌜readReturnAddress args = 0x14ccc⌝ ∗
      ⌜readSizeSlot args = (readBufferSlot args + 8)%Z⌝ ∗
      ⌜Z.modulo (readBufferSlot args) 8 = 0⌝ ∗
      ⌜bv_extract 0 3 bufferSlot = BV 3 0⌝ ∗
      ⌜bv_extract 0 3 sizeSlot = BV 3 0⌝ ∗
      ⌜((mapRamBase defaultMap) <= readBufferSlot args)%Z⌝ ∗
      ⌜(readSizeSlot args < (machineRamEnd defaultMap))%Z⌝ ∗
      ⌜((mapRamBase defaultMap) <= bv_unsigned bufferSlot)%Z⌝ ∗
      ⌜(bv_unsigned bufferSlot < (machineRamEnd defaultMap))%Z⌝ ∗
      ⌜(bv_unsigned sizeSlot < (machineRamEnd defaultMap))%Z⌝ ∗
      ⌜bv_unsigned sizeWord = Z.of_nat (length (readInputBytes args))⌝ ∗
      ⌜(length (readInputBytes args) <= maxSszInputSize)%nat⌝ ∗
      reg_col zesu_ram_sys_regs ∗
      "x1" ↦ᵣ RVal_Bits (BV 64 0x14ccc) ∗
      "x5" ↦ᵣ RVal_Bits old_x5 ∗
      "x6" ↦ᵣ RVal_Bits old_x6 ∗
      "x10" ↦ᵣ RVal_Bits bufferSlot ∗
      "x11" ↦ᵣ RVal_Bits sizeSlot ∗
      bv_unsigned (bufferSlot + (BV 64 0)) ↦ₘ oldBufferSlot ∗
      bv_unsigned (sizeSlot + (BV 64 0)) ↦ₘ oldSizeSlot ∗
      bv_unsigned (readInputIoPointer + (BV 64 0)) ↦ₘ sizeWord ∗
      (mapInputBufferAddress defaultMap) ↦ₘ∗ readInputMemory (readInputBytes args) ∗
      readSavedFrameAddress args ↦ₘ savedWord ∗
      ⌜bv_unsigned savedWord = readSavedReturnAddress args⌝ ∗ True)%I;
  islarisExit := fun args outcome =>
    (∃ (bufferSlot sizeSlot sizeWord savedWord : bv 64),
      ⌜bv_unsigned bufferSlot = readBufferSlot args⌝ ∗
      ⌜bv_unsigned sizeSlot = readSizeSlot args⌝ ∗
      ⌜outcome = Build_ReadInputOutcome (mapInputBufferAddress defaultMap)⌝ ∗
      ⌜bv_unsigned sizeWord = Z.of_nat (length (readInputBytes args))⌝ ∗
      ⌜bv_unsigned savedWord = readSavedReturnAddress args⌝ ∗
      reg_col zesu_ram_sys_regs ∗
      "x1" ↦ᵣ RVal_Bits (BV 64 0x14ccc) ∗
      "x5" ↦ᵣ RVal_Bits (BV 64 (mapIoContextAddress defaultMap)) ∗
      "x6" ↦ᵣ RVal_Bits sizeWord ∗
      "x10" ↦ᵣ RVal_Bits bufferSlot ∗
      "x11" ↦ᵣ RVal_Bits sizeSlot ∗
      bv_unsigned (bufferSlot + (BV 64 0)) ↦ₘ (BV 64 (mapInputBufferAddress defaultMap)) ∗
      bv_unsigned (sizeSlot + (BV 64 0)) ↦ₘ sizeWord ∗
      bv_unsigned (readInputIoPointer + (BV 64 0)) ↦ₘ sizeWord ∗
      (mapInputBufferAddress defaultMap) ↦ₘ∗ readInputMemory (readInputBytes args) ∗
      readSavedFrameAddress args ↦ₘ savedWord ∗ True)%I
|}.

Definition readInputAllows
    (_ : ReadInputArgs) (outcome : ReadInputOutcome) : Prop :=
  readInputAddress outcome = (mapInputBufferAddress defaultMap).

