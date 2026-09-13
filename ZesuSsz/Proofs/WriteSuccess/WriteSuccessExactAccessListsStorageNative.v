Require Import ZesuSsz.Automation.All.
Require Import ZesuSsz.Automation.Continuations.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessExactAccessListsStorageEntry.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessExactAccessListsBranchEntry.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessExactAccessListsStorageWholeBranch.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessExactAccessListsCountEntry.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessExactAccessListsSpec.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessExactStorageKeysNativeEntry.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessExactStorageKeysNative.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessStorageKeysSpec.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessAccessListsSpec.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessExactTransactionsGasLoads.
Require Import isla.riscv64.riscv64.

Lemma access_storage_exact_loop_native `{!islaG Sigma} `{!threadG}
    sp base entries processed entry rest bytes storedIndex x19 savedX22 x22 x27 tail
    (P : iProp Sigma) :
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
  instr_body 0x153b4 (writeSuccessStorageKeysLoopExit x19 sp
     (bv_unsigned (writeSuccessAccessEntryStoragePointer entry))
     (writeSuccessAccessEntryStorageCount entry) (writeSuccessAccessEntryStorageBytes entry)
     (writeSuccessExactAccessListsEvents sp rest tail) (accessStorageLoopFrame sp base entries processed entry rest bytes savedX22 P)) -∗
  instr_body 0x15228 (accessListsStorageWholeBranchPost sp (sp - BV 64 16)%bv
    (writeSuccessAccessEntryBytes entry)
    (accessBranchLoopFrame sp base entries processed (entry :: rest) bytes storedIndex x19 savedX22
      (Z_to_bv 64 (Z.of_nat (length entries))) x22 x27 tail
      (accessEntryAfterCountEvents sp entry rest tail) P) ∗
    ⌜transactionRowWord (writeSuccessAccessEntryBytes entry) 0 8 <> BV 64 0⌝ ∗ True).
Proof.
  iStartProof. iIntros "#H58 #H59 #H60 #H61 #H62 #Houtput Hnext".
  iAssert (∀ n : nat, instr_body 0x15228 (storageKeysExactEntry x19 sp
    (writeSuccessAccessEntryStoragePointer entry) n (writeSuccessAccessEntryStorageBytes entry)
    (writeSuccessExactAccessListsEvents sp rest tail) (accessStorageLoopFrame sp base entries processed entry rest bytes savedX22 P)))%I as "Hall".
  { iIntros (n). iApply (storage_keys_exact_native_correct with "H58 H59 H60 H61 H62 Houtput"). }
  iPoseProof (instr_body_exists 0x15228 _ with "Hall") as "Hbody".
  iApply (instr_pre_wand 0x15228 0x15228 false false with "Hbody");
    [done | reflexivity |].
  iIntros "(Hpost & Hne & _)".
  iApply access_storage_loop_entry_resources. iFrame "Hpost Hne".
  iSplitL "Hnext"; last done.
  iApply (instr_pre_wand 0x153b4 0x153b4 false true with "Hnext");
    [done | reflexivity |].
  iIntros "$".
Qed.
Print Assumptions access_storage_exact_loop_native.
