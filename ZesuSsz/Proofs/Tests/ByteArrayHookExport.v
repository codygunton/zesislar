Require Import ZesuSsz.Automation.All.
Require Import ZesuMachineMap.Machine.
From Coq Require Import Lists.List.
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Automation.BitvectorFacts.
From IslaTraces.write_success_32 Require Import a15048.


Lemma test_all_exports_byte_array_hooks `{!islaG Sigma} `{!threadG}
    (base : bv 64) (bytes : list (bv 8)) :
  length bytes = 288%nat ->
  instr 0x15048 (Some a15048) -∗
  instr_body 0x15048 (
    reg_col zesu_sys_regs ∗
    "x10" ↦ᵣ RVal_Bits base ∗
    "x16" ↦ᵣ: (fun _ => True) ∗
    ⌜bv_unsigned base `mod` 8 = 0⌝ ∗
    ⌜(mapRamBase defaultMap) <= bv_unsigned base ∧
      bv_unsigned base + 288 <= (machineRamEnd defaultMap)⌝ ∗
    bv_unsigned base ↦ₘ∗ bytes ∗
    instr_pre 0x1504c (
      reg_col zesu_sys_regs ∗
      "x10" ↦ᵣ RVal_Bits base ∗
      "x16" ↦ᵣ RVal_Bits
        (Z_to_bv 64
          (little_endian_to_bv 8 (take 8 (drop 80 bytes)))) ∗
      bv_unsigned base ↦ₘ∗ bytes ∗ True) ∗ True).
Proof.
  move => Hlength.
  iStartProof.
  zesu_run.
  Unshelve. all: prepare_sidecond.
  all: try bv_solve.
  all: try lia.
Qed.

Print Assumptions test_all_exports_byte_array_hooks.
