Require Import ZesuSsz.Automation.All.
Require Import ZesuMachineMap.Machine.
Require Import ZesuSsz.Automation.StackArrayIndices.
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Contracts.IslarisMachine.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessExactTransactionsGasLoads.
From IslaTraces.write_success_76 Require Import instrs.
Local Remove Hints IslaTraces.write_success_76.a155a4_spec.a155a4_spec_inst : typeclass_instances.
Local Remove Hints IslaTraces.write_success_76.a155a8_spec.a155a8_spec_inst : typeclass_instances.
Local Remove Hints IslaTraces.write_success_76.a155ac_spec.a155ac_spec_inst : typeclass_instances.
Local Remove Hints IslaTraces.write_success_76.a155b0_spec.a155b0_spec_inst : typeclass_instances.

Definition authorizationWordsEntry `{!islaG Sigma} `{!threadG}
    (sp : bv 64) (bytes : list (bv 8)) (P : iProp Sigma) : iProp Sigma :=
  (reg_col zesu_ram_sys_regs ∗
   reg_col [(KindReg "x10", BitsShape 64); (KindReg "x11", BitsShape 64);
     (KindReg "x12", BitsShape 64); (KindReg "x13", BitsShape 64)] ∗
   "x2" ↦ᵣ RVal_Bits sp ∗ (bv_unsigned sp + 1744) ↦ₘ∗ bytes ∗
   ⌜length bytes = 144%nat⌝ ∗ ⌜bv_unsigned sp `mod` 16 = 0⌝ ∗
   ⌜((mapRamBase defaultMap) <= bv_unsigned sp)%Z⌝ ∗
   ⌜(bv_unsigned sp + 1896 < (machineRamEnd defaultMap))%Z⌝ ∗ P ∗ True)%I.
Global Instance : LithiumUnfold (@authorizationWordsEntry) := I.

Definition authorizationWordsAtPost `{!islaG Sigma} `{!threadG}
    (sp : bv 64) (bytes : list (bv 8)) (offset : nat) (P : iProp Sigma) : iProp Sigma :=
  (reg_col zesu_ram_sys_regs ∗
   "x10" ↦ᵣ RVal_Bits (transactionRowWord bytes offset 0) ∗
   "x11" ↦ᵣ RVal_Bits (transactionRowWord bytes offset 8) ∗
   "x12" ↦ᵣ RVal_Bits (transactionRowWord bytes offset 16) ∗
   "x13" ↦ᵣ RVal_Bits (transactionRowWord bytes offset 24) ∗
   "x2" ↦ᵣ RVal_Bits sp ∗ (bv_unsigned sp + 1744) ↦ₘ∗ bytes ∗
   ⌜length bytes = 144%nat⌝ ∗ ⌜bv_unsigned sp `mod` 16 = 0⌝ ∗
   ⌜((mapRamBase defaultMap) <= bv_unsigned sp)%Z⌝ ∗
   ⌜(bv_unsigned sp + 1896 < (machineRamEnd defaultMap))%Z⌝ ∗ P ∗ True)%I.
Global Instance : LithiumUnfold (@authorizationWordsAtPost) := I.

Definition authorizationWordsPost `{!islaG Sigma} `{!threadG}
    (sp : bv 64) (bytes : list (bv 8)) (P : iProp Sigma) : iProp Sigma :=
  authorizationWordsAtPost sp bytes 0 P.
Global Instance : LithiumUnfold (@authorizationWordsPost) := I.

Lemma authorization_words_correct `{!islaG Sigma} `{!threadG} sp bytes (P : iProp Sigma) :
  ([∗ list] instruction ∈ take 4 IslaTraces.write_success_76.instrs.instr_map,
    instr instruction.1 (Some instruction.2))%I -∗
  instr_body 0x155b4 (authorizationWordsPost sp bytes P) -∗
  instr_body 0x155a4 (authorizationWordsEntry sp bytes P).
Proof.
  zesu_block.
  all: unfold transactionRowWord; zesu_normalize_stack_array_indices; reflexivity.
Qed.
Print Assumptions authorization_words_correct.
