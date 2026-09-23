Require Import ZesuSsz.Automation.All.
Require Import isla.riscv64.riscv64.
From ZesuSsz.Proofs.WriteSuccess Require Import
  WriteSuccessExactAccessListsSpec WriteSuccessExactAccessListsControl
  WriteSuccessExactAccessListsControlEntry WriteSuccessExactAccessListsControlReturn.
From IslaTraces.write_success_52 Require Import instrs.

Lemma access_initial_to_loop_correct `{!islaG Sigma} `{!threadG}
    sp base entries bytes storedIndex x19 savedX22 data old11 x22 x27 tail (P : iProp Sigma) :
  ([∗ list] instruction ∈ IslaTraces.write_success_52.instrs.instr_map,
    instr instruction.1 (Some instruction.2))%I -∗
  □ instr_pre 0x151d4 (writeSuccessExactAccessListsState sp base entries [] entries bytes
    storedIndex x19 savedX22 data x22 x27 tail P) -∗
  instr_body 0x151d0 (accessListsControlState sp (Z_to_bv 64 (Z.of_nat (length entries))) old11 data
    (accessControlFrame sp base entries [] entries bytes storedIndex x19 savedX22 data x22 x27 tail P)).
Proof. move => *. zesu_block. Qed.
Print Assumptions access_initial_to_loop_correct.
