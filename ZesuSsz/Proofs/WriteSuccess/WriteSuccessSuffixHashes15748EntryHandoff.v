Require Import ZesuSsz.Automation.AllLegacy.
Require Import ZesuMachineMap.Machine.
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Contracts.IslarisMachine.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessEvents.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessHashesLoop.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessLoopCommon.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessSuffixHashes15748Compose.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessSuffixHashesQContinuations.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessSuffixHashesEntryResources.

Lemma write_success_suffix_hashes_entry_15748_handoff
    `{!islaG Sigma} `{!threadG}
    (P : iProp Sigma)
    (sp pointer : bv 64) (base : Z)
    (total processed remaining : nat) (bytes : list (bv 8))
    (tail : spec) :
  instr_pre 0x15748
    (writeSuccessSuffixHashes15748NonzeroSpec
      sp (Z_to_bv 64 (Z.of_nat (S remaining)))
      (writeSuccessHashesEvents sp (S remaining) tail)
      (writeSuccessSuffixHashesEntryLoopFrame
        sp pointer base total processed remaining bytes tail P)) -∗
  instr_pre 0x15748
    (reg_col zesu_ram_sys_regs ∗
     "x8" ↦ᵣ RVal_Bits (Z_to_bv 64 (Z.of_nat (S remaining))) ∗
     "x10" ↦ᵣ RVal_Bits (Z_to_bv 64 (Z.of_nat (S remaining))) ∗
     (bv_unsigned sp - 16) ↦ₘ? 16 ∗
     mmio_range (machineOutputAddress defaultMap) 16 ∗
     spec_trace
       (writeOutputEventsAny (sp - BV 64 16)%bv (BV 64 8)
         (writeSuccessHashesEvents sp (S remaining) tail)) ∗
     writeSuccessSuffixHashesEntryFrame
       sp pointer base total processed remaining bytes tail P).
Proof. move => *. zesu_block. Qed.
