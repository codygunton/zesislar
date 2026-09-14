Require Import ZesuSsz.Automation.All.
Require Import ZesuMachineMap.Machine.
Require Import ZesuSsz.Automation.CounterZero.
Require Import isla.riscv64.riscv64.
From ZesuSsz.Proofs.WriteSuccess Require Import
  WriteSuccessExactAuthorizationsLoopSpec WriteSuccessExactAuthorizationsModel.

Definition authorizationInitialFrame `{!islaG Sigma} `{!threadG}
    (sp : bv 64) (base : Z) (P : iProp Sigma) : iProp Sigma :=
  ((bv_unsigned sp + 168) ↦ₘ (Z_to_bv 64 base) ∗ P ∗ True)%I.
Global Instance : LithiumUnfold (@authorizationInitialFrame) := I.

Definition authorizationInitialEntry `{!islaG Sigma} `{!threadG}
    (sp oldra old5 : bv 64) (base : Z) (row : list (bv 8))
    (rest : list (list (bv 8))) source tail (P : iProp Sigma) : iProp Sigma :=
  (reg_col zesu_ram_sys_regs ∗ "x2" ↦ᵣ RVal_Bits sp ∗
   "x1" ↦ᵣ RVal_Bits oldra ∗ "x5" ↦ᵣ RVal_Bits old5 ∗
   reg_col [(KindReg "x8", BitsShape 64); (KindReg "x9", BitsShape 64)] ∗
   "x18" ↦ᵣ RVal_Bits (Z_to_bv 64 (Z.of_nat (S (length rest)))) ∗
   reg_col [(KindReg "x10", BitsShape 64); (KindReg "x11", BitsShape 64);
     (KindReg "x12", BitsShape 64); (KindReg "x13", BitsShape 64);
     (KindReg "x14", BitsShape 64); (KindReg "x15", BitsShape 64)] ∗
   base ↦ₘ∗ source ∗ (bv_unsigned sp + 1744) ↦ₘ? 144 ∗
   (bv_unsigned sp - 48) ↦ₘ? 48 ∗ mmio_range (machineOutputAddress defaultMap) 16 ∗
   spec_trace (writeSuccessExactAuthorizationEvents sp (row :: rest) tail) ∗
   authorizationInitialFrame sp base P ∗
   instr_pre 0x15620 (authorizationLoopExit sp base source tail
     (authorizationInitialFrame sp base P)) ∗ True)%I.
Global Instance : LithiumUnfold (@authorizationInitialEntry) := I.

Lemma authorization_initial_nonempty `{!islaG Sigma} `{!threadG}
    sp oldra old5 base row rest source tail (P : iProp Sigma) :
  authorizationLoopFacts sp (Z_to_bv 64 base) base (row :: rest) [] row rest source ->
  ([∗ list] instruction ∈ IslaTraces.write_success_74.instrs.instr_map,
    instr instruction.1 (Some instruction.2))%I -∗
  □ instr_pre 0x15590 (authorizationLoopSpec sp base (row :: rest) source tail
    (authorizationInitialFrame sp base P)) -∗
  instr_body 0x15584 (authorizationInitialEntry sp oldra old5 base row rest source tail P).
Proof.
  intros Hfacts. pose proof Hfacts as Hbounds.
  destruct Hbounds as (Hrows & Hall & Hbytes & Hposition & Hcount & Halign & Hlow & Hhigh & Hbase & Hend).
  zesu_block.
  liInst (fun x => x.1ₗ = row /\ x.2ₗ = []).
  zesu_run.
Qed.
Print Assumptions authorization_initial_nonempty.
