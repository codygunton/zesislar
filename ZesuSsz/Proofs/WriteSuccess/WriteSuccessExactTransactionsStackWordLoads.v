Require Import ZesuSsz.Automation.All.
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Contracts.IslarisMachine.
From IslaTraces.write_success_29 Require Import instrs.

Definition transactionsStackWordLoadEntry `{!islaG Sigma} `{!threadG}
    (pointer sp : bv 64) (bytes : list (bv 8)) (P : iProp Sigma) : iProp Sigma :=
  (reg_col zesu_ram_sys_regs ∗ "x10" ↦ᵣ RVal_Bits pointer ∗ "x2" ↦ᵣ RVal_Bits sp ∗
   reg_col [(KindReg "x11", BitsShape 64)] ∗ (bv_unsigned sp + 224) ↦ₘ? 24 ∗
   bv_unsigned pointer ↦ₘ∗ bytes ∗ ⌜length bytes = 288%nat⌝ ∗
   ⌜bv_unsigned pointer `mod` 8 = 0⌝ ∗
   ⌜0x20000000 <= bv_unsigned pointer⌝ ∗ ⌜bv_unsigned pointer + 288 < 0x40000000⌝ ∗
   ⌜bv_unsigned sp `mod` 8 = 0⌝ ∗ ⌜0x20000000 <= bv_unsigned sp⌝ ∗
   ⌜bv_unsigned sp + 248 < 0x40000000⌝ ∗ P ∗ True)%I.
Global Instance : LithiumUnfold (@transactionsStackWordLoadEntry) := I.

Definition transactionsStackWordLoadPost `{!islaG Sigma} `{!threadG}
    (pointer sp : bv 64) (bytes : list (bv 8)) (P : iProp Sigma) : iProp Sigma :=
  (reg_col zesu_ram_sys_regs ∗ "x10" ↦ᵣ RVal_Bits pointer ∗ "x2" ↦ᵣ RVal_Bits sp ∗
   "x11" ↦ᵣ RVal_Bits (Z_to_bv 64 (little_endian_to_bv 8 (take 8 (drop 152 bytes)))) ∗
   (bv_unsigned sp + 224) ↦ₘ Z_to_bv 64 (little_endian_to_bv 8 (take 8 (drop 152 bytes))) ∗
   (bv_unsigned sp + 232) ↦ₘ Z_to_bv 64 (little_endian_to_bv 8 (take 8 (drop 144 bytes))) ∗
   (bv_unsigned sp + 240) ↦ₘ Z_to_bv 64 (little_endian_to_bv 8 (take 8 (drop 136 bytes))) ∗
   bv_unsigned pointer ↦ₘ∗ bytes ∗ ⌜length bytes = 288%nat⌝ ∗
   ⌜bv_unsigned pointer `mod` 8 = 0⌝ ∗
   ⌜0x20000000 <= bv_unsigned pointer⌝ ∗ ⌜bv_unsigned pointer + 288 < 0x40000000⌝ ∗
   ⌜bv_unsigned sp `mod` 8 = 0⌝ ∗ ⌜0x20000000 <= bv_unsigned sp⌝ ∗
   ⌜bv_unsigned sp + 248 < 0x40000000⌝ ∗ P ∗ True)%I.
Global Instance : LithiumUnfold (@transactionsStackWordLoadPost) := I.

Lemma transactions_stack_word_loads_correct `{!islaG Sigma} `{!threadG}
    pointer sp bytes (P : iProp Sigma) :
  ([∗ list] instruction ∈ take 6 (drop 9 IslaTraces.write_success_29.instrs.instr_map),
    instr instruction.1 (Some instruction.2))%I -∗
  □ instr_pre 0x14f44 (transactionsStackWordLoadPost pointer sp bytes P) -∗
  instr_body 0x14f2c (transactionsStackWordLoadEntry pointer sp bytes P).
Proof.
  iStartProof. iIntros "#Hcode #Hnext".
  iEval (rewrite /IslaTraces.write_success_29.instrs.instr_map /=) in "Hcode".
  iDestruct "Hcode" as "#(H0 & H1 & H2 & H3 & H4 & H5 & _)".
  zesu_run.
Qed.
Print Assumptions transactions_stack_word_loads_correct.
