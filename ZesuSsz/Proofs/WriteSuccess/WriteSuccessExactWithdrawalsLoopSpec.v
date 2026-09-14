Require Import ZesuSsz.Automation.All.
Require Import ZesuMachineMap.Machine.
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Contracts.IslarisMachine.
Require Import ZesuSsz.Export.Snapshots.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessExactWithdrawalsModel.
From Coq Require Import Lists.List ZArith.ZArith.

Definition withdrawalLoopFacts (sp pointer : bv 64) (base : Z)
    (rows prefix : list (list (bv 8))) (row : list (bv 8))
    (rest : list (list (bv 8))) (source : list (bv 8)) : Prop :=
  rows = prefix ++ row :: rest /\
  Forall (fun bytes => length bytes = 48%nat) rows /\ source = concat rows /\
  bv_unsigned pointer = (base + 48 * Z.of_nat (length prefix))%Z /\
  (Z.of_nat (S (length rest)) < 18446744073709551616)%Z /\
  bv_unsigned sp `mod` 16 = 0 /\ ((mapRamBase defaultMap) <= bv_unsigned sp - 48)%Z /\
  (bv_unsigned sp + 1896 < (machineRamEnd defaultMap))%Z /\
  ((mapRamBase defaultMap) <= base)%Z /\ (base + Z.of_nat (length source) < (machineRamEnd defaultMap))%Z.

Definition withdrawalLoopExit `{!islaG Sigma} `{!threadG}
    (sp : bv 64) (base : Z) (source : list (bv 8))
    (tail : spec) (P : iProp Sigma) : iProp Sigma :=
  (reg_col zesu_ram_sys_regs ∗ "x2" ↦ᵣ RVal_Bits sp ∗
   "x1" ↦ᵣ RVal_Bits (BV 64 0x156dc) ∗ "x5" ↦ᵣ RVal_Bits (BV 64 (mapIoContextAddress defaultMap)) ∗
   "x18" ↦ᵣ RVal_Bits (sp + BV 64 1768)%bv ∗
   "x8" ↦ᵣ RVal_Bits (Z_to_bv 64 (base + Z.of_nat (length source))) ∗
   "x9" ↦ᵣ RVal_Bits (BV 64 0) ∗
   reg_col [(KindReg "x10", BitsShape 64); (KindReg "x11", BitsShape 64);
     (KindReg "x12", BitsShape 64); (KindReg "x13", BitsShape 64);
     (KindReg "x14", BitsShape 64); (KindReg "x15", BitsShape 64)] ∗
   base ↦ₘ∗ source ∗ (bv_unsigned sp + 1744) ↦ₘ? 48 ∗
   (bv_unsigned sp - 16) ↦ₘ? 16 ∗ mmio_range (machineOutputAddress defaultMap) 16 ∗
   spec_trace tail ∗ P ∗ True)%I.
Global Instance : LithiumUnfold (@withdrawalLoopExit) := I.

Definition withdrawalLoopPayload `{!islaG Sigma} `{!threadG}
    (sp pointer : bv 64) (base : Z) (rows prefix : list (list (bv 8)))
    (row : list (bv 8)) (rest : list (list (bv 8))) (source : list (bv 8))
    (tail : spec) (P : iProp Sigma) : iProp Sigma :=
  ("x2" ↦ᵣ RVal_Bits sp ∗ "x18" ↦ᵣ RVal_Bits (sp + BV 64 1768)%bv ∗
   reg_col [(KindReg "x10", BitsShape 64); (KindReg "x11", BitsShape 64);
     (KindReg "x12", BitsShape 64); (KindReg "x13", BitsShape 64);
     (KindReg "x14", BitsShape 64); (KindReg "x15", BitsShape 64)] ∗
   base ↦ₘ∗ source ∗ (bv_unsigned sp + 1744) ↦ₘ? 48 ∗
   (bv_unsigned sp - 16) ↦ₘ? 16 ∗ mmio_range (machineOutputAddress defaultMap) 16 ∗
   spec_trace (writeSuccessExactWithdrawalEvents sp (row :: rest) tail) ∗ P ∗
   ⌜withdrawalLoopFacts sp pointer base rows prefix row rest source⌝ ∗
   instr_pre 0x156e8 (withdrawalLoopExit sp base source tail P) ∗ True)%I.
Global Instance : LithiumUnfold (@withdrawalLoopPayload) := I.

Definition withdrawalLoopSpec `{!islaG Sigma} `{!threadG}
    (sp : bv 64) (base : Z) (rows : list (list (bv 8))) (source : list (bv 8))
    (tail : spec) (P : iProp Sigma) : iProp Sigma :=
  (∃ prefix row rest (pointer oldra old5 : bv 64),
   reg_col zesu_ram_sys_regs ∗ "x1" ↦ᵣ RVal_Bits oldra ∗ "x5" ↦ᵣ RVal_Bits old5 ∗
   "x8" ↦ᵣ RVal_Bits pointer ∗ "x9" ↦ᵣ RVal_Bits (Z_to_bv 64 (Z.of_nat (S (length rest)))) ∗
   withdrawalLoopPayload sp pointer base rows prefix row rest source tail P ∗ True)%I.
Global Instance : LithiumUnfold (@withdrawalLoopSpec) := I.

Definition withdrawalBodyFrame `{!islaG Sigma} `{!threadG}
    (sp pointer : bv 64) (base : Z) (rows prefix : list (list (bv 8)))
    (row : list (bv 8)) (rest : list (list (bv 8))) (source : list (bv 8))
    (tail : spec) (P : iProp Sigma) : iProp Sigma :=
  ("x8" ↦ᵣ RVal_Bits pointer ∗
   "x9" ↦ᵣ RVal_Bits (Z_to_bv 64 (Z.of_nat (S (length rest)))) ∗
   reg_col [(KindReg "x12", BitsShape 64); (KindReg "x13", BitsShape 64);
     (KindReg "x14", BitsShape 64); (KindReg "x15", BitsShape 64)] ∗
   base ↦ₘ∗ source ∗ P ∗
   ⌜withdrawalLoopFacts sp pointer base rows prefix row rest source⌝ ∗
   instr_pre 0x156e8 (withdrawalLoopExit sp base source tail P) ∗ True)%I.
Global Instance : LithiumUnfold (@withdrawalBodyFrame) := I.

Definition withdrawalCopyCallerFrame `{!islaG Sigma} `{!threadG}
    (sp pointer old5 : bv 64) (base : Z) (rows prefix : list (list (bv 8)))
    (row : list (bv 8)) (rest : list (list (bv 8))) (source : list (bv 8))
    (tail : spec) (P : iProp Sigma) : iProp Sigma :=
  ("x5" ↦ᵣ RVal_Bits old5 ∗ "x18" ↦ᵣ RVal_Bits (sp + BV 64 1768)%bv ∗
   "x9" ↦ᵣ RVal_Bits (Z_to_bv 64 (Z.of_nat (S (length rest)))) ∗
   (bv_unsigned sp - 16) ↦ₘ? 16 ∗ mmio_range (machineOutputAddress defaultMap) 16 ∗
   spec_trace (writeSuccessExactWithdrawalEvents sp (row :: rest) tail) ∗ P ∗
   ⌜withdrawalLoopFacts sp pointer base rows prefix row rest source⌝ ∗
   instr_pre 0x156e8 (withdrawalLoopExit sp base source tail P) ∗ True)%I.
Global Instance : LithiumUnfold (@withdrawalCopyCallerFrame) := I.

Definition withdrawalTailPayload `{!islaG Sigma} `{!threadG}
    (sp pointer : bv 64) (base : Z) (rows prefix : list (list (bv 8)))
    (row : list (bv 8)) (rest : list (list (bv 8))) (source : list (bv 8))
    (tail : spec) (P : iProp Sigma) : iProp Sigma :=
  ("x2" ↦ᵣ RVal_Bits sp ∗ "x1" ↦ᵣ RVal_Bits (BV 64 0x156dc) ∗
   "x5" ↦ᵣ RVal_Bits (BV 64 (mapIoContextAddress defaultMap)) ∗ "x18" ↦ᵣ RVal_Bits (sp + BV 64 1768)%bv ∗
   reg_col [(KindReg "x10", BitsShape 64); (KindReg "x11", BitsShape 64);
     (KindReg "x12", BitsShape 64); (KindReg "x13", BitsShape 64);
     (KindReg "x14", BitsShape 64); (KindReg "x15", BitsShape 64)] ∗
   base ↦ₘ∗ source ∗ (bv_unsigned sp + 1744) ↦ₘ? 48 ∗
   (bv_unsigned sp - 16) ↦ₘ? 16 ∗ mmio_range (machineOutputAddress defaultMap) 16 ∗
   spec_trace (writeSuccessExactWithdrawalEvents sp rest tail) ∗ P ∗
   ⌜withdrawalLoopFacts sp pointer base rows prefix row rest source⌝ ∗
   instr_pre 0x156e8 (withdrawalLoopExit sp base source tail P) ∗ True)%I.
Global Instance : LithiumUnfold (@withdrawalTailPayload) := I.

Require Import ZesuSsz.Proofs.WriteSuccess.FixedRowsLayout.
Lemma withdrawal_facts_layout sp pointer base rows prefix row rest source :
  withdrawalLoopFacts sp pointer base rows prefix row rest source ->
  Forall (fun bytes => length bytes = 48%nat) prefix /\ length row = 48%nat /\
  take 48 (drop (48 * length prefix) source) = row /\
  length source = (48 * (length prefix + S (length rest)))%nat.
Proof.
  intros (Hrows & Hall & Hsource & Hposition & Hcount & Halign & Hlow & Hhigh & Hbase & Hend).
  rewrite Hrows Forall_app in Hall. destruct Hall as [Hprefix Hremaining].
  inversion Hremaining as [|? ? Hrow Hrest].
  destruct (fixed_rows_layout 48 prefix row rest Hprefix Hrow) as [HprefixLength Hslice].
  destruct (fixed_rows_layout 48 rest row [] Hrest Hrow) as [HrestLength _].
  repeat split; try assumption.
  - rewrite Hsource Hrows. exact Hslice.
  - rewrite Hsource Hrows concat_app app_length /= app_length HprefixLength HrestLength Hrow. lia.
Qed.
Print Assumptions withdrawal_facts_layout.
