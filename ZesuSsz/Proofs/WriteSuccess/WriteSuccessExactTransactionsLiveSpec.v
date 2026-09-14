Require Import ZesuSsz.Automation.All.
Require Import ZesuMachineMap.Machine.
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Contracts.IslarisMachine.
From ZesuSsz.Proofs.WriteSuccess Require Import
  WriteSuccessExactTransactionsSpec WriteSuccessTransactionsSpec.

Definition transactionLoopSourceFacts (sp : bv 64) (base : Z)
    (transactions processed remaining : list writeSuccessTransaction)
    (bytes : list (bv 8)) : Prop :=
  transactions = processed ++ remaining /\
  bytes = writeSuccessTransactionsBytes transactions /\
  length bytes = (288 * length transactions)%nat /\
  (length transactions < 2 ^ 64)%nat /\ bv_unsigned sp `mod` 16 = 0 /\
  (mapRamBase defaultMap) <= bv_unsigned sp - 48 /\ bv_unsigned sp + 1896 < (machineRamEnd defaultMap) /\
  base `mod` 8 = 0 /\ (mapRamBase defaultMap) <= base /\
  base + Z.of_nat (length bytes) < (machineRamEnd defaultMap).

(** Only the transaction working ranges become uninitialized scratch.
    The caller retains its live stack copies through [P]. *)
Definition transactionLiveScratch `{!islaG Sigma}
    (sp : bv 64) (base : Z) (total : nat) : iProp Sigma :=
  ((bv_unsigned sp - 48) ↦ₘ? 48 ∗
   (bv_unsigned sp + 104) ↦ₘ Z_to_bv 64 base ∗
   (bv_unsigned sp + 112) ↦ₘ Z_to_bv 64 (Z.of_nat total) ∗
   (bv_unsigned sp + 120) ↦ₘ? 160 ∗
   (bv_unsigned sp + 1640) ↦ₘ? 256 ∗ True)%I.
Global Instance : LithiumUnfold (@transactionLiveScratch) := I.

Definition transactionLiveLoopState `{!islaG Sigma} `{!threadG}
    (sp : bv 64) (base : Z)
    (transactions processed remaining : list writeSuccessTransaction)
    (bytes : list (bv 8)) (tail : spec) (P : iProp Sigma) : iProp Sigma :=
  (reg_col zesu_ram_sys_regs ∗ reg_col writeSuccessTransactionsOtherRegShapes ∗
   "x2" ↦ᵣ RVal_Bits sp ∗
   "x10" ↦ᵣ RVal_Bits (Z_to_bv 64 (Z.of_nat (length transactions))) ∗
   "x11" ↦ᵣ RVal_Bits (Z_to_bv 64 (Z.of_nat (length processed))) ∗
   base ↦ₘ∗ bytes ∗ writeSuccessTransactionsOwn transactions ∗
   transactionLiveScratch sp base (length transactions) ∗
   mmio_range (machineOutputAddress defaultMap) 16 ∗
   spec_trace (writeSuccessExactTransactionsEvents sp remaining tail) ∗
   ⌜transactionLoopSourceFacts sp base transactions processed remaining bytes⌝ ∗ P ∗ True)%I.
Global Instance : LithiumUnfold (@transactionLiveLoopState) := I.

Definition transactionLiveLoopExit `{!islaG Sigma} `{!threadG}
    (sp : bv 64) (base : Z) (transactions : list writeSuccessTransaction)
    (bytes : list (bv 8)) (tail : spec) (P : iProp Sigma) : iProp Sigma :=
  (reg_col zesu_ram_sys_regs ∗ reg_col writeSuccessTransactionsOtherRegShapes ∗
   "x2" ↦ᵣ RVal_Bits sp ∗
   "x10" ↦ᵣ RVal_Bits (Z_to_bv 64 (Z.of_nat (length transactions))) ∗
   "x11" ↦ᵣ RVal_Bits (Z_to_bv 64 (Z.of_nat (length transactions))) ∗
   base ↦ₘ∗ bytes ∗ writeSuccessTransactionsOwn transactions ∗
   transactionLiveScratch sp base (length transactions) ∗
   mmio_range (machineOutputAddress defaultMap) 16 ∗ spec_trace tail ∗ P ∗ True)%I.
Global Instance : LithiumUnfold (@transactionLiveLoopExit) := I.

Lemma transactions_live_state_exit `{!islaG Sigma} `{!threadG}
    sp base transactions bytes tail (P : iProp Sigma) :
  transactionLiveLoopState sp base transactions transactions [] bytes tail P -∗
  transactionLiveLoopExit sp base transactions bytes tail P.
Proof.
  iIntros "Hstate".
  rewrite /transactionLiveLoopState /transactionLiveLoopExit
    /writeSuccessExactTransactionsEvents /writeSuccessExactTransactionsPayloads /=.
  iDestruct "Hstate" as "(Hsys & Hregs & Hsp & H10 & H11 & Hbytes & Hown & Hscratch & Hmmio & Htrace & %Hfacts & HP & _)".
  iFrame.
Qed.
Print Assumptions transactions_live_state_exit.
