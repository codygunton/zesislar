Require Import ZesuSsz.Automation.All.
Require Import ZesuMachineMap.Machine.
Require Import ZesuSsz.Automation.ArrayByteValues.
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Contracts.IslarisMachine.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessExactTransactionsFlagLoads.
From IslaTraces.write_success_67 Require Import instrs.
Local Remove Hints IslaTraces.write_success_67.a15434_spec.a15434_spec_inst : typeclass_instances.

Definition blobPairs16Entry `{!islaG Sigma} `{!threadG}
    (a b c d e f : bv 8) (P : iProp Sigma) : iProp Sigma :=
  (reg_col zesu_ram_sys_regs ∗
   "x6" ↦ᵣ RVal_Bits (bv_zero_extend 64 a) ∗
   "x7" ↦ᵣ RVal_Bits (bv_zero_extend 64 b) ∗
   "x28" ↦ᵣ RVal_Bits (bv_zero_extend 64 c) ∗
   "x8" ↦ᵣ RVal_Bits (bv_zero_extend 64 d) ∗
   "x9" ↦ᵣ RVal_Bits (bv_zero_extend 64 e) ∗
   "x18" ↦ᵣ RVal_Bits (bv_zero_extend 64 f) ∗ P ∗ True)%I.
Global Instance : LithiumUnfold (@blobPairs16Entry) := I.

Definition blobPairs16Post `{!islaG Sigma} `{!threadG}
    (a b c d e f : bv 8) (P : iProp Sigma) : iProp Sigma :=
  (reg_col zesu_ram_sys_regs ∗
   "x6" ↦ᵣ RVal_Bits (Z_to_bv 64 (bv_unsigned a + bv_unsigned b * 256)) ∗
   "x7" ↦ᵣ RVal_Bits (Z_to_bv 64
     (bv_unsigned c * 65536 + bv_unsigned d * 16777216)) ∗
   "x28" ↦ᵣ RVal_Bits (Z_to_bv 64 (bv_unsigned e + bv_unsigned f * 256)) ∗
   "x8" ↦ᵣ RVal_Bits (Z_to_bv 64 (bv_unsigned d * 16777216)) ∗
   "x9" ↦ᵣ RVal_Bits (bv_zero_extend 64 e) ∗
   "x18" ↦ᵣ RVal_Bits (Z_to_bv 64 (bv_unsigned f * 256)) ∗ P ∗ True)%I.
Global Instance : LithiumUnfold (@blobPairs16Post) := I.


Definition blobByte15EntryFrame `{!islaG Sigma} `{!threadG}
    (row : bv 64) (base : Z) (bytes : list (bv 8)) (index : nat)
    (P : iProp Sigma) : iProp Sigma :=
  (reg_col [(KindReg "x25", BitsShape 64)] ∗
   "x19" ↦ᵣ RVal_Bits row ∗ base ↦ₘ∗ bytes ∗
   ⌜(bv_unsigned row = base + Z.of_nat index)%Z⌝ ∗
   ⌜(index + 16 <= length bytes)%nat⌝ ∗ ⌜((mapRamBase defaultMap) <= base)%Z⌝ ∗
   ⌜(base + Z.of_nat (length bytes) < (machineRamEnd defaultMap))%Z⌝ ∗ P ∗ True)%I.
Global Instance : LithiumUnfold (@blobByte15EntryFrame) := I.

Definition blobByte15PostFrame `{!islaG Sigma} `{!threadG}
    (row : bv 64) (base : Z) (bytes : list (bv 8)) (index : nat)
    (P : iProp Sigma) : iProp Sigma :=
  ("x25" ↦ᵣ RVal_Bits (transactionRowByte bytes index 15) ∗
   "x19" ↦ᵣ RVal_Bits row ∗ base ↦ₘ∗ bytes ∗
   ⌜(bv_unsigned row = base + Z.of_nat index)%Z⌝ ∗
   ⌜(index + 16 <= length bytes)%nat⌝ ∗ ⌜((mapRamBase defaultMap) <= base)%Z⌝ ∗
   ⌜(base + Z.of_nat (length bytes) < (machineRamEnd defaultMap))%Z⌝ ∗ P ∗ True)%I.
Global Instance : LithiumUnfold (@blobByte15PostFrame) := I.

Lemma blob_pairs_load16_correct `{!islaG Sigma} `{!threadG}
    a b c d e f row base bytes index (P : iProp Sigma) :
  ([∗ list] instruction ∈ take 8 IslaTraces.write_success_67.instrs.instr_map,
    instr instruction.1 (Some instruction.2))%I -∗
  instr_body 0x15454 (blobPairs16Post a b c d e f
    (blobByte15PostFrame row base bytes index P)) -∗
  instr_body 0x15434 (blobPairs16Entry a b c d e f
    (blobByte15EntryFrame row base bytes index P)).
Proof.
  zesu_block.
  all: first [apply array_byte_pair_shift_value | apply array_byte_pair_shift_value16 |
    unfold transactionRowByte; zesu_array_byte_value].
Qed.
Print Assumptions blob_pairs_load16_correct.
