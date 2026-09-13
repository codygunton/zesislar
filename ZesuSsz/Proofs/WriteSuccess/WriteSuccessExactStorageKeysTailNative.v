Require Import ZesuSsz.Automation.All.
Require Import ZesuSsz.Automation.CounterShapes.
Require Import ZesuSsz.Automation.CounterZero.
Require Import isla.riscv64.riscv64.
From iris.proofmode Require Import environments.
From ZesuSsz.Proofs.WriteSuccess Require Import
  WriteSuccessExactStorageKeysTail WriteSuccessExactStorageKeysLoopReturn
  WriteSuccessExactStorageKeysSpec WriteSuccessExactStorageKeysCounter
  WriteSuccessExactStorageKeysModel WriteSuccessStorageKeysSpec WriteSuccessLoopCommon.
From IslaTraces.write_success_62 Require Import instrs.

Lemma storage_keys_tail_native `{!islaG Sigma} `{!threadG}
    (x19 sp pointer : bv 64) base total processed remaining bytes tail (P : iProp Sigma) :
  ([∗ list] instruction ∈ IslaTraces.write_success_62.instrs.instr_map,
    instr instruction.1 (Some instruction.2))%I -∗
  □ instr_pre 0x15228 (writeSuccessExactStorageKeysLoopSpec x19 P) -∗
  instr_body 0x153a8 (storageKeysTailState pointer
    (Z_to_bv 64 (Z.of_nat (S remaining)))
    (storageKeysTailFrame x19 sp pointer base total processed remaining bytes tail P)).
Proof.
  zesu_block.
  liInst (fun x => x.1ₗ = tail /\ x.2ₗ = bytes /\ x.3ₗ = S processed /\
    x.4ₗ = (processed + S (S n))%nat /\ x.5ₗ = base).
  zesu_run.
Qed.
Print Assumptions storage_keys_tail_native.
