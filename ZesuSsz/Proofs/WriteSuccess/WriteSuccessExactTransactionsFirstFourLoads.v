Require Import ZesuSsz.Automation.All.
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Contracts.IslarisMachine.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessTransactionsSpec.
From IslaTraces.write_success_29 Require Import instrs.

Definition transactionsFirstFourLoadEntry `{!islaG Sigma} `{!threadG}
    (pointer : bv 64) (bytes : list (bv 8)) (P : iProp Sigma) : iProp Sigma :=
  (reg_col zesu_ram_sys_regs ∗ "x10" ↦ᵣ RVal_Bits pointer ∗
   reg_col [(KindReg "x25", BitsShape 64); (KindReg "x24", BitsShape 64);
     (KindReg "x9", BitsShape 64); (KindReg "x23", BitsShape 64)] ∗
   bv_unsigned pointer ↦ₘ∗ bytes ∗ ⌜length bytes = 288%nat⌝ ∗
   ⌜bv_unsigned pointer `mod` 8 = 0⌝ ∗
   ⌜0x20000000 <= bv_unsigned pointer⌝ ∗ ⌜bv_unsigned pointer + 288 < 0x40000000⌝ ∗ P ∗ True)%I.
Global Instance : LithiumUnfold (@transactionsFirstFourLoadEntry) := I.

Definition transactionsFirstFourLoadPost `{!islaG Sigma} `{!threadG}
    (pointer : bv 64) (bytes : list (bv 8)) (P : iProp Sigma) : iProp Sigma :=
  (reg_col zesu_ram_sys_regs ∗ "x10" ↦ᵣ RVal_Bits pointer ∗
   "x25" ↦ᵣ RVal_Bits (Z_to_bv 64 (little_endian_to_bv 8 (take 8 bytes))) ∗
   "x24" ↦ᵣ RVal_Bits (Z_to_bv 64 (little_endian_to_bv 8 (take 8 (drop 8 bytes)))) ∗
   "x9" ↦ᵣ RVal_Bits (Z_to_bv 64 (little_endian_to_bv 8 (take 8 (drop 16 bytes)))) ∗
   "x23" ↦ᵣ RVal_Bits (Z_to_bv 64 (little_endian_to_bv 8 (take 8 (drop 24 bytes)))) ∗
   bv_unsigned pointer ↦ₘ∗ bytes ∗ ⌜length bytes = 288%nat⌝ ∗
   ⌜bv_unsigned pointer `mod` 8 = 0⌝ ∗
   ⌜0x20000000 <= bv_unsigned pointer⌝ ∗ ⌜bv_unsigned pointer + 288 < 0x40000000⌝ ∗ P ∗ True)%I.
Global Instance : LithiumUnfold (@transactionsFirstFourLoadPost) := I.

Lemma transactions_first_four_loads_correct `{!islaG Sigma} `{!threadG}
    pointer bytes (P : iProp Sigma) :
  ([∗ list] instruction ∈ take 4 (drop 5 IslaTraces.write_success_29.instrs.instr_map),
    instr instruction.1 (Some instruction.2))%I -∗
  □ instr_pre 0x14f2c (transactionsFirstFourLoadPost pointer bytes P) -∗
  instr_body 0x14f1c (transactionsFirstFourLoadEntry pointer bytes P).
Proof.
  iStartProof. iIntros "#Hcode #Hnext".
  iEval (rewrite /IslaTraces.write_success_29.instrs.instr_map /=) in "Hcode".
  iDestruct "Hcode" as "#(H0 & H1 & H2 & H3 & _)".
  zesu_run.
Qed.
Print Assumptions transactions_first_four_loads_correct.
