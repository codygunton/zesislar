Require Import ZesuSsz.Automation.All.
Require Import ZesuMachineMap.Machine.
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Contracts.IslarisMachine.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessExactTransactionsGasLoads.
From IslaTraces.write_success_57 Require Import instrs.

Definition accessListsStorageWholeBranchEntry `{!islaG Sigma} `{!threadG}
    (sp data : bv 64) (bytes : list (bv 8)) (P : iProp Sigma) : iProp Sigma :=
  (reg_col zesu_ram_sys_regs ∗ "x2" ↦ᵣ RVal_Bits sp ∗
   "x10" ↦ᵣ RVal_Bits data ∗
   reg_col [(KindReg "x22", BitsShape 64); (KindReg "x27", BitsShape 64)] ∗
   (bv_unsigned sp + 1744) ↦ₘ∗ bytes ∗ ⌜length bytes = 40%nat⌝ ∗
   ⌜bv_unsigned sp `mod` 8 = 0⌝ ∗ ⌜(mapRamBase defaultMap) <= bv_unsigned sp⌝ ∗
   ⌜bv_unsigned sp + 1784 < (machineRamEnd defaultMap)⌝ ∗ P ∗ True)%I.
Global Instance : LithiumUnfold (@accessListsStorageWholeBranchEntry) := I.

Definition accessListsStorageWholeBranchPost `{!islaG Sigma} `{!threadG}
    (sp data : bv 64) (bytes : list (bv 8)) (P : iProp Sigma) : iProp Sigma :=
  (reg_col zesu_ram_sys_regs ∗ "x2" ↦ᵣ RVal_Bits sp ∗
   "x10" ↦ᵣ RVal_Bits data ∗
   "x22" ↦ᵣ RVal_Bits (transactionRowWord bytes 0 0) ∗
   "x27" ↦ᵣ RVal_Bits (transactionRowWord bytes 0 8) ∗
   (bv_unsigned sp + 1744) ↦ₘ∗ bytes ∗ ⌜length bytes = 40%nat⌝ ∗
   ⌜bv_unsigned sp `mod` 8 = 0⌝ ∗ ⌜(mapRamBase defaultMap) <= bv_unsigned sp⌝ ∗
   ⌜bv_unsigned sp + 1784 < (machineRamEnd defaultMap)⌝ ∗ P ∗ True)%I.
Global Instance : LithiumUnfold (@accessListsStorageWholeBranchPost) := I.

Lemma access_lists_storage_whole_branch_correct `{!islaG Sigma} `{!threadG}
    sp data bytes (P : iProp Sigma) :
  ([∗ list] instruction ∈ IslaTraces.write_success_57.instrs.instr_map,
    instr instruction.1 (Some instruction.2))%I -∗
  instr_body 0x15228 (accessListsStorageWholeBranchPost sp data bytes P ∗
    ⌜transactionRowWord bytes 0 8 <> BV 64 0⌝ ∗ True) -∗
  instr_body 0x153b4 (accessListsStorageWholeBranchPost sp data bytes P ∗
    ⌜transactionRowWord bytes 0 8 = BV 64 0⌝ ∗ True) -∗
  instr_body 0x1521c (accessListsStorageWholeBranchEntry sp data bytes P).
Proof.
  zesu_block.
  all: have Hfirst : bv_unsigned (sp + BV 64 1744)%bv -
      (bv_unsigned sp + 1744) = 0 by bv_solve.
  all: have Hsecond : bv_unsigned (sp + BV 64 1752)%bv -
      (bv_unsigned sp + 1744) = 8 by bv_solve.
  all: rewrite ?Hfirst ?Hsecond; unfold transactionRowWord; cbn; try done.
  all: match goal with
    | Hbranch : context[Z.to_nat _] |- _ => rewrite Hsecond in Hbranch; exact Hbranch
    end.
Qed.
Print Assumptions access_lists_storage_whole_branch_correct.
