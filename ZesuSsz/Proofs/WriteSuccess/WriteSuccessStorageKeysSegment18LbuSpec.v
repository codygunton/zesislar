Require Import ZesuSsz.Automation.All.
Require Import ZesuMachineMap.Machine.
Require Import isla.riscv64.riscv64.
Require Import IslaTraces.write_success_60.a152e8.
Require Import ZesuSsz.Contracts.IslarisMachine.

Definition writeSuccessStorageKeysLbuSpec
    `{!islaG Sigma} `{!threadG} (pc : Z) : iProp Sigma :=
  ∃ (base : bv 64) (byte : bv 8),
  reg_col zesu_instr_sys_regs ∗
  "x1" ↦ᵣ: (fun _ => True)%I ∗
  "x22" ↦ᵣ RVal_Bits base ∗
  (bv_unsigned base + 3) ↦ₘ byte ∗
  ⌜(mapRamBase defaultMap) <= bv_unsigned base + 3 < (machineRamEnd defaultMap)⌝ ∗
  instr_pre (pc + 4)
    (reg_col zesu_instr_sys_regs ∗
     "x1" ↦ᵣ RVal_Bits (bv_zero_extend 64 byte) ∗
     "x22" ↦ᵣ RVal_Bits base ∗
     (bv_unsigned base + 3) ↦ₘ byte ∗ True) ∗ True.

Global Instance : LithiumUnfold (@writeSuccessStorageKeysLbuSpec) := I.

Lemma write_success_storage_keys_segment18_lbu_spec
    `{!islaG Sigma} `{!threadG} (pc : Z) :
  instr pc (Some IslaTraces.write_success_60.a152e8.a152e8) ⊢
  instr_body pc (writeSuccessStorageKeysLbuSpec pc).
Proof.
  iStartProof.
  liARun.
  Unshelve. all: prepare_sidecond.
  all: try bv_solve.
  all: try lia.
  Show Existentials.
Qed.
