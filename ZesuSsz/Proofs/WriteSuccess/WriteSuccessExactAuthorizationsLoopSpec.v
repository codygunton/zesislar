Require Import ZesuSsz.Automation.All.
Require Import ZesuMachineMap.Machine.
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Contracts.IslarisMachine.
Require Import ZesuSsz.Export.Snapshots.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessExactAuthorizationsModel.
From Coq Require Import Lists.List ZArith.ZArith.

Definition authorizationLoopFacts (sp pointer : bv 64) (base : Z)
    (rows prefix : list (list (bv 8))) (row : list (bv 8))
    (rest : list (list (bv 8))) (source : list (bv 8)) : Prop :=
  rows = prefix ++ row :: rest /\
  Forall (fun bytes => length bytes = 144%nat) rows /\ source = concat rows /\
  bv_unsigned pointer = (base + 144 * Z.of_nat (length prefix))%Z /\
  (Z.of_nat (S (length rest)) < 18446744073709551616)%Z /\
  bv_unsigned sp `mod` 16 = 0 /\ ((mapRamBase defaultMap) <= bv_unsigned sp - 48)%Z /\
  (bv_unsigned sp + 1896 < (machineRamEnd defaultMap))%Z /\
  ((mapRamBase defaultMap) <= base)%Z /\ (base + Z.of_nat (length source) < (machineRamEnd defaultMap))%Z.

Definition authorizationLoopExit `{!islaG Sigma} `{!threadG}
    (sp : bv 64) (base : Z) (source : list (bv 8))
    (tail : spec) (P : iProp Sigma) : iProp Sigma :=
  (reg_col zesu_ram_sys_regs ∗ "x2" ↦ᵣ RVal_Bits sp ∗
   "x1" ↦ᵣ RVal_Bits (BV 64 0x15614) ∗ "x5" ↦ᵣ RVal_Bits (BV 64 (mapIoContextAddress defaultMap)) ∗
   "x8" ↦ᵣ RVal_Bits (sp + BV 64 1856)%bv ∗
   "x9" ↦ᵣ RVal_Bits (Z_to_bv 64 (base + Z.of_nat (length source))) ∗
   "x18" ↦ᵣ RVal_Bits (BV 64 0) ∗
   reg_col [(KindReg "x10", BitsShape 64); (KindReg "x11", BitsShape 64);
     (KindReg "x12", BitsShape 64); (KindReg "x13", BitsShape 64);
     (KindReg "x14", BitsShape 64); (KindReg "x15", BitsShape 64)] ∗
   base ↦ₘ∗ source ∗ (bv_unsigned sp + 1744) ↦ₘ? 144 ∗
   (bv_unsigned sp - 48) ↦ₘ? 48 ∗ mmio_range (machineOutputAddress defaultMap) 16 ∗
   spec_trace tail ∗ P ∗ True)%I.
Global Instance : LithiumUnfold (@authorizationLoopExit) := I.

Definition authorizationLoopPayload `{!islaG Sigma} `{!threadG}
    (sp pointer : bv 64) (base : Z) (rows prefix : list (list (bv 8)))
    (row : list (bv 8)) (rest : list (list (bv 8))) (source : list (bv 8))
    (tail : spec) (P : iProp Sigma) : iProp Sigma :=
  ("x2" ↦ᵣ RVal_Bits sp ∗ "x8" ↦ᵣ RVal_Bits (sp + BV 64 1856)%bv ∗
   reg_col [(KindReg "x10", BitsShape 64); (KindReg "x11", BitsShape 64);
     (KindReg "x12", BitsShape 64); (KindReg "x13", BitsShape 64);
     (KindReg "x14", BitsShape 64); (KindReg "x15", BitsShape 64)] ∗
   base ↦ₘ∗ source ∗ (bv_unsigned sp + 1744) ↦ₘ? 144 ∗
   (bv_unsigned sp - 48) ↦ₘ? 48 ∗ mmio_range (machineOutputAddress defaultMap) 16 ∗
   spec_trace (writeSuccessExactAuthorizationEvents sp (row :: rest) tail) ∗ P ∗
   ⌜authorizationLoopFacts sp pointer base rows prefix row rest source⌝ ∗
   instr_pre 0x15620 (authorizationLoopExit sp base source tail P) ∗ True)%I.
Global Instance : LithiumUnfold (@authorizationLoopPayload) := I.

Definition authorizationLoopSpec `{!islaG Sigma} `{!threadG}
    (sp : bv 64) (base : Z) (rows : list (list (bv 8))) (source : list (bv 8))
    (tail : spec) (P : iProp Sigma) : iProp Sigma :=
  (∃ prefix row rest (pointer oldra old5 : bv 64),
   reg_col zesu_ram_sys_regs ∗ "x1" ↦ᵣ RVal_Bits oldra ∗ "x5" ↦ᵣ RVal_Bits old5 ∗
   "x9" ↦ᵣ RVal_Bits pointer ∗ "x18" ↦ᵣ RVal_Bits (Z_to_bv 64 (Z.of_nat (S (length rest)))) ∗
   authorizationLoopPayload sp pointer base rows prefix row rest source tail P ∗ True)%I.
Global Instance : LithiumUnfold (@authorizationLoopSpec) := I.

Definition authorizationBodyFrame `{!islaG Sigma} `{!threadG}
    (sp pointer : bv 64) (base : Z) (rows prefix : list (list (bv 8)))
    (row : list (bv 8)) (rest : list (list (bv 8))) (source : list (bv 8))
    (tail : spec) (P : iProp Sigma) : iProp Sigma :=
  ("x9" ↦ᵣ RVal_Bits pointer ∗
   "x18" ↦ᵣ RVal_Bits (Z_to_bv 64 (Z.of_nat (S (length rest)))) ∗
   reg_col [(KindReg "x14", BitsShape 64); (KindReg "x15", BitsShape 64)] ∗
   base ↦ₘ∗ source ∗ P ∗
   ⌜authorizationLoopFacts sp pointer base rows prefix row rest source⌝ ∗
   instr_pre 0x15620 (authorizationLoopExit sp base source tail P) ∗ True)%I.
Global Instance : LithiumUnfold (@authorizationBodyFrame) := I.

Definition authorizationCopyCallerFrame `{!islaG Sigma} `{!threadG}
    (sp pointer old5 : bv 64) (base : Z) (rows prefix : list (list (bv 8)))
    (row : list (bv 8)) (rest : list (list (bv 8))) (source : list (bv 8))
    (tail : spec) (P : iProp Sigma) : iProp Sigma :=
  ("x5" ↦ᵣ RVal_Bits old5 ∗ "x8" ↦ᵣ RVal_Bits (sp + BV 64 1856)%bv ∗
   "x18" ↦ᵣ RVal_Bits (Z_to_bv 64 (Z.of_nat (S (length rest)))) ∗
   (bv_unsigned sp - 48) ↦ₘ? 48 ∗ mmio_range (machineOutputAddress defaultMap) 16 ∗
   spec_trace (writeSuccessExactAuthorizationEvents sp (row :: rest) tail) ∗ P ∗
   ⌜authorizationLoopFacts sp pointer base rows prefix row rest source⌝ ∗
   instr_pre 0x15620 (authorizationLoopExit sp base source tail P) ∗ True)%I.
Global Instance : LithiumUnfold (@authorizationCopyCallerFrame) := I.

Definition authorizationTailPayload `{!islaG Sigma} `{!threadG}
    (sp pointer : bv 64) (base : Z) (rows prefix : list (list (bv 8)))
    (row : list (bv 8)) (rest : list (list (bv 8))) (source : list (bv 8))
    (tail : spec) (P : iProp Sigma) : iProp Sigma :=
  ("x2" ↦ᵣ RVal_Bits sp ∗ "x1" ↦ᵣ RVal_Bits (BV 64 0x15614) ∗
   "x5" ↦ᵣ RVal_Bits (BV 64 (mapIoContextAddress defaultMap)) ∗ "x8" ↦ᵣ RVal_Bits (sp + BV 64 1856)%bv ∗
   reg_col [(KindReg "x10", BitsShape 64); (KindReg "x11", BitsShape 64);
     (KindReg "x12", BitsShape 64); (KindReg "x13", BitsShape 64);
     (KindReg "x14", BitsShape 64); (KindReg "x15", BitsShape 64)] ∗
   base ↦ₘ∗ source ∗ (bv_unsigned sp + 1744) ↦ₘ? 144 ∗
   (bv_unsigned sp - 48) ↦ₘ? 48 ∗ mmio_range (machineOutputAddress defaultMap) 16 ∗
   spec_trace (writeSuccessExactAuthorizationEvents sp rest tail) ∗ P ∗
   ⌜authorizationLoopFacts sp pointer base rows prefix row rest source⌝ ∗
   instr_pre 0x15620 (authorizationLoopExit sp base source tail P) ∗ True)%I.
Global Instance : LithiumUnfold (@authorizationTailPayload) := I.
