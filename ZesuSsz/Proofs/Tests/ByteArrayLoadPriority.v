Require Import ZesuSsz.Automation.All.
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Automation.Sets.call.
From IslaTraces.write_success_blocks Require Import Index.

Definition byteLoadState `{!islaG Sigma} `{!threadG}
    (row : bv 64) (base : Z) (bytes : list (bv 8)) (index : nat) : iProp Sigma :=
  (reg_col zesu_ram_sys_regs ∗ "x19" ↦ᵣ RVal_Bits row ∗
   reg_col [(KindReg "x28", BitsShape 64)] ∗ base ↦ₘ∗ bytes ∗
   ⌜(base + Z.of_nat (length bytes) < 1073741824)%Z⌝ ∗
   ⌜0 ≤ base⌝ ∗
   ⌜(index + 20 <= length bytes)%nat⌝ ∗
   ⌜(bv_unsigned row = base + Z.of_nat index)%Z⌝ ∗ True)%I.
Global Instance : LithiumUnfold (@byteLoadState) := I.
Global Typeclasses Opaque byteLoadState.
Lemma test_byte_load `{!islaG Sigma} `{!threadG}
    (row : bv 64) (base : Z) (bytes : list (bv 8)) (index : nat) :
  instr_lookup_resources IslaTraces.write_success_blocks.Index.lookup -∗
  IslaTraces.write_success_blocks.Index.spec_instr_resources -∗
  instr_pre 0x153e0 (byteLoadState row base bytes index) -∗
  instr_body 0x153dc (byteLoadState row base bytes index).
Proof. zesu_block. Qed.
Print Assumptions test_byte_load.
