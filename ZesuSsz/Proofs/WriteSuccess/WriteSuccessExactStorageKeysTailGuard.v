Require Import ZesuSsz.Automation.All.
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessExactStorageKeysTail.
From IslaTraces.write_success_62 Require Import instrs.

Lemma storage_keys_tail_pre_correct `{!islaG Sigma} `{!threadG}
    pointer count (P : iProp Sigma) :
  ([∗ list] instruction ∈ IslaTraces.write_success_62.instrs.instr_map,
    instr instruction.1 (Some instruction.2))%I -∗
  instr_pre 0x15228 (storageKeysTailState (pointer + BV 64 32)%bv
    (count - BV 64 1)%bv P ∗ ⌜(count - BV 64 1)%bv <> BV 64 0⌝ ∗ True) -∗
  instr_pre 0x153b4 (storageKeysTailState (pointer + BV 64 32)%bv
    (count - BV 64 1)%bv P ∗ ⌜(count - BV 64 1)%bv = BV 64 0⌝ ∗ True) -∗
  instr_body 0x153a8 (storageKeysTailState pointer count P).
Proof.
  zesu_block.
  all: replace (count - BV 64 1)%bv
    with (count + BV 64 18446744073709551615)%bv by bv_solve; assumption.
Qed.
Print Assumptions storage_keys_tail_pre_correct.
