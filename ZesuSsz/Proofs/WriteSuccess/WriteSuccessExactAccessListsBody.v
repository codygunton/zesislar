Require Import ZesuSsz.Automation.All.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessExactAccessListsCopyNative.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessExactAccessListsOutputNative.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessExactAccessListsCountNative.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessExactAccessListsStorageDispatch.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessExactAccessListsStorageEntry.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessExactAccessListsSpec.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessStorageKeysSpec.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessAccessListsSpec.
Require Import isla.riscv64.riscv64.

Lemma access_exact_iteration_correct `{!islaG Sigma} `{!threadG}
    sp base entries processed entry rest bytes storedIndex x19 savedX22 x22 x27 tail
    (P : iProp Sigma) :
  ([∗ list] instruction ∈ IslaTraces.write_success_54.instrs.instr_map,
    instr instruction.1 (Some instruction.2))%I -∗
  ([∗ list] instruction ∈ IslaTraces.write_success_55.instrs.instr_map,
    instr instruction.1 (Some instruction.2))%I -∗
  ([∗ list] instruction ∈ IslaTraces.write_success_56.instrs.instr_map,
    instr instruction.1 (Some instruction.2))%I -∗
  ([∗ list] instruction ∈ IslaTraces.write_success_57.instrs.instr_map,
    instr instruction.1 (Some instruction.2))%I -∗
  ([∗ list] instruction ∈ IslaTraces.write_success_58.instrs.instr_map,
    instr instruction.1 (Some instruction.2))%I -∗
  ([∗ list] instruction ∈ IslaTraces.write_success_59.instrs.instr_map,
    instr instruction.1 (Some instruction.2))%I -∗
  ([∗ list] instruction ∈ IslaTraces.write_success_60.instrs.instr_map,
    instr instruction.1 (Some instruction.2))%I -∗
  ([∗ list] instruction ∈ IslaTraces.write_success_61.instrs.instr_map,
    instr instruction.1 (Some instruction.2))%I -∗
  ([∗ list] instruction ∈ IslaTraces.write_success_62.instrs.instr_map,
    instr instruction.1 (Some instruction.2))%I -∗
  ([∗ list] instruction ∈ IslaTraces.write_success_02.instrs.instr_map,
    instr instruction.1 (Some instruction.2))%I -∗
  ([∗ list] instruction ∈ IslaTraces.write_success_07.instrs.instr_map,
    instr instruction.1 (Some instruction.2))%I -∗
  ([∗ list] instruction ∈ IslaTraces.write_success_01.instrs.instr_map,
    instr instruction.1 (Some instruction.2))%I -∗
  □ instr_body 0x153b4 (writeSuccessStorageKeysLoopExit x19 sp
    (bv_unsigned (writeSuccessAccessEntryStoragePointer entry))
    (writeSuccessAccessEntryStorageCount entry) (writeSuccessAccessEntryStorageBytes entry)
    (writeSuccessExactAccessListsEvents sp rest tail)
    (accessStorageLoopFrame sp base entries processed entry rest bytes savedX22 P)) -∗
  instr_body 0x151dc (writeSuccessExactAccessListsState sp base entries processed (entry :: rest)
    bytes storedIndex x19 savedX22 (Z_to_bv 64 (Z.of_nat (length entries))) x22 x27 tail P).
Proof.
  iStartProof. iIntros "#H54 #H55 #H56 #H57 #H58 #H59 #H60 #H61 #H62 #Hcopy #Hencoder #Houtput #Hnext".
  iApply (access_copy_exact_loop_native with "H54 Hcopy").
  iApply (access_output_exact_loop_native with "H55 Houtput").
  iApply (access_count_exact_loop_native with "H56 Hencoder Houtput").
  iApply (access_storage_exact_dispatch with "H57 H58 H59 H60 H61 H62 Houtput Hnext").
Qed.
Print Assumptions access_exact_iteration_correct.
