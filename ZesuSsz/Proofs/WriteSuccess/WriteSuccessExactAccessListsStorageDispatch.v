Require Import ZesuSsz.Automation.All.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessExactAccessListsStorageEntry.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessExactAccessListsStorageNative.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessExactAccessListsStorageZero.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessExactAccessListsBranchNative.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessExactAccessListsCountEntry.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessExactAccessListsCountWhole.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessExactAccessListsSpec.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessStorageKeysSpec.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessAccessListsSpec.
Require Import isla.riscv64.riscv64.

Lemma access_storage_exact_dispatch `{!islaG Sigma} `{!threadG}
    sp base entries processed entry rest bytes storedIndex x19 savedX22 x22 x27 tail
    (P : iProp Sigma) :
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
  ([∗ list] instruction ∈ IslaTraces.write_success_01.instrs.instr_map,
    instr instruction.1 (Some instruction.2))%I -∗
  □ instr_body 0x153b4 (writeSuccessStorageKeysLoopExit x19 sp
    (bv_unsigned (writeSuccessAccessEntryStoragePointer entry))
    (writeSuccessAccessEntryStorageCount entry) (writeSuccessAccessEntryStorageBytes entry)
    (writeSuccessExactAccessListsEvents sp rest tail)
    (accessStorageLoopFrame sp base entries processed entry rest bytes savedX22 P)) -∗
  instr_body 0x1521c (accessCountWholePost sp (writeSuccessAccessEntryBytes entry)
    (accessEntryAfterCountEvents sp entry rest tail)
    (accessCountLoopFrame sp base entries processed (entry :: rest) bytes storedIndex x19 savedX22
      (Z_to_bv 64 (Z.of_nat (length entries))) x22 x27 tail P)).
Proof.
  iStartProof. iIntros "#H57 #H58 #H59 #H60 #H61 #H62 #Houtput #Hnext".
  iApply (access_branch_exact_loop_native with "H57").
  - iApply (access_storage_exact_loop_native with "H58 H59 H60 H61 H62 Houtput Hnext").
  - iApply (instr_pre_wand 0x153b4 0x153b4 false false with "Hnext");
      [done | reflexivity |].
    iApply access_storage_zero_resources.
Qed.
Print Assumptions access_storage_exact_dispatch.
