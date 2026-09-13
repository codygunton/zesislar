Require Import ZesuSsz.Automation.All.
Require Import ZesuSsz.Automation.Continuations.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessExactAccessListsCountEntry.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessExactAccessListsCountWhole.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessExactAccessListsBranchEntry.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessExactAccessListsStorageWholeBranch.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessExactTransactionsGasLoads.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessAccessListsSpec.
Require Import isla.riscv64.riscv64.

Lemma access_branch_exact_loop_native `{!islaG Sigma} `{!threadG}
    sp base entries processed entry rest bytes storedIndex x19 savedX22 x22 x27 tail
    (P : iProp Sigma) :
  ([∗ list] instruction ∈ IslaTraces.write_success_57.instrs.instr_map,
    instr instruction.1 (Some instruction.2))%I -∗
  instr_body 0x15228 (accessListsStorageWholeBranchPost sp (sp - BV 64 16)%bv
    (writeSuccessAccessEntryBytes entry) (accessBranchLoopFrame sp base entries processed (entry :: rest) bytes storedIndex x19 savedX22
      (Z_to_bv 64 (Z.of_nat (length entries))) x22 x27 tail
      (accessEntryAfterCountEvents sp entry rest tail) P) ∗
    ⌜transactionRowWord (writeSuccessAccessEntryBytes entry) 0 8 <> BV 64 0⌝ ∗ True) -∗
  instr_body 0x153b4 (accessListsStorageWholeBranchPost sp (sp - BV 64 16)%bv
    (writeSuccessAccessEntryBytes entry) (accessBranchLoopFrame sp base entries processed (entry :: rest) bytes storedIndex x19 savedX22
      (Z_to_bv 64 (Z.of_nat (length entries))) x22 x27 tail
      (accessEntryAfterCountEvents sp entry rest tail) P) ∗
    ⌜transactionRowWord (writeSuccessAccessEntryBytes entry) 0 8 = BV 64 0⌝ ∗ True) -∗
  instr_body 0x1521c (accessCountWholePost sp (writeSuccessAccessEntryBytes entry)
    (accessEntryAfterCountEvents sp entry rest tail)
    (accessCountLoopFrame sp base entries processed (entry :: rest) bytes storedIndex x19 savedX22
      (Z_to_bv 64 (Z.of_nat (length entries))) x22 x27 tail P)).
Proof.
  iStartProof. iIntros "#Hcode Hpositive Hzero".
  iPoseProof (access_lists_storage_whole_branch_correct sp (sp - BV 64 16)%bv
    (writeSuccessAccessEntryBytes entry) (accessBranchLoopFrame sp base entries processed (entry :: rest) bytes storedIndex x19 savedX22
      (Z_to_bv 64 (Z.of_nat (length entries))) x22 x27 tail
      (accessEntryAfterCountEvents sp entry rest tail) P)
    with "Hcode Hpositive Hzero") as "Hbody".
  iApply (instr_pre_wand 0x1521c 0x1521c false false with "Hbody");
    [done | reflexivity |].
  iApply access_branch_loop_entry_resources.
Qed.
Print Assumptions access_branch_exact_loop_native.
