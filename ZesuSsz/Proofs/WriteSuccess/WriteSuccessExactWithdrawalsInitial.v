Require Import ZesuSsz.Automation.All.
Require Import ZesuMachineMap.Machine.
Require Import ZesuSsz.Automation.CounterZero.
Require Import isla.riscv64.riscv64.
From ZesuSsz.Proofs.WriteSuccess Require Import
  WriteSuccessExactWithdrawalsLoopSpec WriteSuccessExactWithdrawalsModel.

Definition withdrawalInitialEntry `{!islaG Sigma} `{!threadG}
    (sp oldra old5 : bv 64) (base : Z) (row : list (bv 8))
    (rest : list (list (bv 8))) source tail (P : iProp Sigma) : iProp Sigma :=
  (reg_col zesu_ram_sys_regs ∗ "x2" ↦ᵣ RVal_Bits sp ∗
   "x1" ↦ᵣ RVal_Bits oldra ∗ "x5" ↦ᵣ RVal_Bits old5 ∗
   "x8" ↦ᵣ RVal_Bits (Z_to_bv 64 base) ∗
   "x9" ↦ᵣ RVal_Bits (Z_to_bv 64 (Z.of_nat (S (length rest)))) ∗
   reg_col [(KindReg "x18", BitsShape 64); (KindReg "x10", BitsShape 64);
     (KindReg "x11", BitsShape 64); (KindReg "x12", BitsShape 64);
     (KindReg "x13", BitsShape 64); (KindReg "x14", BitsShape 64);
     (KindReg "x15", BitsShape 64)] ∗
   base ↦ₘ∗ source ∗ (bv_unsigned sp + 1744) ↦ₘ? 48 ∗
   (bv_unsigned sp - 16) ↦ₘ? 16 ∗ mmio_range (machineOutputAddress defaultMap) 16 ∗
   spec_trace (writeSuccessExactWithdrawalEvents sp (row :: rest) tail) ∗ P ∗
   instr_pre 0x156e8 (withdrawalLoopExit sp base source tail P) ∗ True)%I.
Global Instance : LithiumUnfold (@withdrawalInitialEntry) := I.

Lemma withdrawal_initial_nonempty `{!islaG Sigma} `{!threadG}
    sp oldra old5 base row rest source tail (P : iProp Sigma) :
  withdrawalLoopFacts sp (Z_to_bv 64 base) base (row :: rest) [] row rest source ->
  ([∗ list] instruction ∈ IslaTraces.write_success_89.instrs.instr_map,
    instr instruction.1 (Some instruction.2))%I -∗
  □ instr_pre 0x15694 (withdrawalLoopSpec sp base (row :: rest) source tail P) -∗
  instr_body 0x1568c (withdrawalInitialEntry sp oldra old5 base row rest source tail P).
Proof.
  intros Hfacts. pose proof Hfacts as Hbounds.
  destruct Hbounds as (Hrows & Hall & Hbytes & Hposition & Hcount & Halign & Hlow & Hhigh & Hbase & Hend).
  zesu_block.
  liInst (fun x => x.1ₗ = row /\ x.2ₗ = []).
  zesu_run.
Qed.
Print Assumptions withdrawal_initial_nonempty.

