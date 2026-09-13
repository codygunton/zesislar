Require Import ZesuSsz.Automation.All.
Require Import ZesuSsz.Automation.CounterShapes.
Require Import ZesuSsz.Automation.CounterZero.
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Contracts.IslarisMachine.
From ZesuSsz.Proofs.WriteSuccess Require Import
  WriteSuccessBlobHashesSpec WriteSuccessLoopCommon WriteSuccessExactBlobHashesModel
  WriteSuccessExactBlobHashesSpec.
From IslaTraces.write_success_65 Require Import instrs.

Definition blobHeaderEntry `{!islaG Sigma} `{!threadG}
    (sp pointer : bv 64) (base : Z) (total : nat) (bytes : list (bv 8))
    (tail : spec) (P : iProp Sigma) : iProp Sigma :=
  (reg_col zesu_ram_sys_regs ∗ reg_col writeSuccessBlobHashesOtherRegShapes ∗
   "x2" ↦ᵣ RVal_Bits sp ∗ "x19" ↦ᵣ RVal_Bits pointer ∗
   "x22" ↦ᵣ RVal_Bits (Z_to_bv 64 (Z.of_nat total)) ∗
   base ↦ₘ∗ bytes ∗ writeSuccessBlobHashesScratch sp ∗ mmio_range 0x2401a0c0 16 ∗
   spec_trace (writeSuccessExactBlobHashesEvents sp 0 total bytes tail) ∗ P ∗
   ⌜length bytes = (32 * total)%nat⌝ ∗ ⌜bv_unsigned pointer = base⌝ ∗
   ⌜(Z.of_nat total < 18446744073709551616)%Z⌝ ∗ ⌜bv_unsigned sp `mod` 16 = 0⌝ ∗
   ⌜(0x20000000 <= bv_unsigned sp)%Z⌝ ∗ ⌜(bv_unsigned sp + 1896 < 0x40000000)%Z⌝ ∗
   ⌜(0x20000000 <= base)%Z⌝ ∗ ⌜(base + Z.of_nat (length bytes) < 0x40000000)%Z⌝ ∗
   instr_pre 0x15564 (writeSuccessBlobHashesLoopExit sp base total bytes tail P) ∗ True)%I.
Global Instance : LithiumUnfold (@blobHeaderEntry) := I.

Lemma blob_header_correct `{!islaG Sigma} `{!threadG}
    sp pointer base total bytes tail (P : iProp Sigma) :
  ([∗ list] instruction ∈ IslaTraces.write_success_65.instrs.instr_map,
    instr instruction.1 (Some instruction.2))%I -∗
  □ instr_pre 0x153d4 (writeSuccessExactBlobHashesLoopSpec sp base total bytes tail P) -∗
  instr_body 0x153d0 (blobHeaderEntry sp pointer base total bytes tail P).
Proof.
  destruct total as [|remaining]; zesu_block.
  liInst (fun x => x.1ₗ = 0%nat).
  zesu_run.
Qed.
Print Assumptions blob_header_correct.
