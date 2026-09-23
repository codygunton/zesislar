Require Import ZesuSsz.Automation.AllLegacy.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessExactAccessListsSpec.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessExactAccessListsControl.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessExactAccessListsControlEntry.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessExactAccessListsControlReturn.
Require Import isla.riscv64.riscv64.
From IslaTraces.write_success_53 Require Import instrs.

Lemma access_control_exact_native_correct `{!islaG Sigma} `{!threadG}
    sp base entries processed remaining bytes storedIndex x19 savedX22 data x22 x27 tail
    (P : iProp Sigma) :
  ([∗ list] instruction ∈ IslaTraces.write_success_53.instrs.instr_map,
    instr instruction.1 (Some instruction.2))%I -∗
  instr_body 0x151dc (writeSuccessExactAccessListsState sp base entries processed remaining bytes
      storedIndex x19 savedX22 (Z_to_bv 64 (Z.of_nat (length entries))) x22 x27 tail P ∗
    ⌜Z_to_bv 64 (Z.of_nat (length processed)) <> Z_to_bv 64 (Z.of_nat (length entries))⌝ ∗ True) -∗
  instr_body 0x153c0 (writeSuccessExactAccessListsState sp base entries processed remaining bytes
      storedIndex x19 savedX22 (Z_to_bv 64 (Z.of_nat (length entries))) x22 x27 tail P ∗
    ⌜Z_to_bv 64 (Z.of_nat (length processed)) = Z_to_bv 64 (Z.of_nat (length entries))⌝ ∗ True) -∗
  instr_body 0x151d4 (writeSuccessExactAccessListsState sp base entries processed remaining bytes
    storedIndex x19 savedX22 data x22 x27 tail P).
Proof. move => *. zesu_block. Qed.
Print Assumptions access_control_exact_native_correct.
