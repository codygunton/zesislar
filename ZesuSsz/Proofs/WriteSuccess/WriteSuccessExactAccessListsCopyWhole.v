Require Import ZesuSsz.Automation.All.
Require Import ZesuSsz.Automation.Calls.
Import FramedContinuations.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessMemcpyWholePublic.
Require Import ZesuSsz.Contracts.IslarisMachine.
Require Import isla.riscv64.riscv64.
From Coq Require Import Lists.List ZArith.ZArith.
From IslaTraces.write_success_54 Require Import instrs.

Definition accessCopyWholeFrame `{!islaG Sigma} `{!threadG}
    (sp base cursor : bv 64) (P : iProp Sigma) : iProp Sigma :=
  ("x2" ↦ᵣ RVal_Bits sp ∗ (bv_unsigned sp + 256) ↦ₘ base ∗
   (bv_unsigned sp + 272) ↦ₘ cursor ∗ P ∗ True)%I.
Global Instance : LithiumUnfold (@accessCopyWholeFrame) := I.

Definition accessCopyWholePost `{!islaG Sigma} `{!threadG}
    (sp base cursor : bv 64) (bytes : list (bv 8)) (P : iProp Sigma) : iProp Sigma :=
  (∃ final13 final14 : bv 64,
   reg_col zesu_ram_sys_regs ∗ "x1" ↦ᵣ RVal_Bits (BV 64 0x15200) ∗
   "x10" ↦ᵣ RVal_Bits (sp + BV 64 1744)%bv ∗
   "x11" ↦ᵣ RVal_Bits (Z_to_bv 64 (bv_unsigned base + 40 * bv_unsigned cursor)) ∗
   "x12" ↦ᵣ RVal_Bits (BV 64 40) ∗ "x13" ↦ᵣ RVal_Bits final13 ∗
   "x14" ↦ᵣ RVal_Bits final14 ∗ "x15" ↦ᵣ RVal_Bits (BV 64 40) ∗
   bv_unsigned base ↦ₘ∗ bytes ∗
   bv_unsigned (sp + BV 64 1744)%bv ↦ₘ∗
     take 40 (drop (40 * Z.to_nat (bv_unsigned cursor)) bytes) ∗
   accessCopyWholeFrame sp base cursor P ∗ True)%I.
Global Instance : LithiumUnfold (@accessCopyWholePost) := I.

Definition accessCopyWholeEntry `{!islaG Sigma} `{!threadG}
    (sp base cursor old_index old_ra : bv 64) (bytes : list (bv 8))
    (P : iProp Sigma) : iProp Sigma :=
  (reg_col zesu_ram_sys_regs ∗ "x2" ↦ᵣ RVal_Bits sp ∗
   "x11" ↦ᵣ RVal_Bits cursor ∗ "x1" ↦ᵣ RVal_Bits old_ra ∗
   reg_col [(KindReg "x10", BitsShape 64); (KindReg "x12", BitsShape 64);
     (KindReg "x13", BitsShape 64); (KindReg "x14", BitsShape 64);
     (KindReg "x15", BitsShape 64)] ∗
   (bv_unsigned sp + 256) ↦ₘ base ∗ (bv_unsigned sp + 272) ↦ₘ old_index ∗
   bv_unsigned base ↦ₘ∗ bytes ∗ (bv_unsigned sp + 1744) ↦ₘ? 40 ∗
   ⌜bv_unsigned sp `mod` 8 = 0⌝ ∗ ⌜0x20000000 <= bv_unsigned sp⌝ ∗
   ⌜bv_unsigned sp + 1784 < 0x40000000⌝ ∗
   ⌜0x20000000 <= bv_unsigned base⌝ ∗
   ⌜bv_unsigned base + Z.of_nat (length bytes) < 0x40000000⌝ ∗
   ⌜(40 * Z.to_nat (bv_unsigned cursor) + 40 <= length bytes)%nat⌝ ∗
   instr_pre 0x15200 (accessCopyWholePost sp base cursor bytes P) ∗ P ∗ True)%I.
Global Instance : LithiumUnfold (@accessCopyWholeEntry) := I.

Lemma access_copy_whole_correct `{!islaG Sigma} `{!threadG}
    sp base cursor old_index old_ra bytes (P : iProp Sigma) :
  ([∗ list] instruction ∈ IslaTraces.write_success_54.instrs.instr_map,
    instr instruction.1 (Some instruction.2))%I -∗
  ([∗ list] instruction ∈ IslaTraces.write_success_02.instrs.instr_map,
    instr instruction.1 (Some instruction.2))%I -∗
  instr_body 0x151dc (accessCopyWholeEntry sp base cursor old_index old_ra bytes P).
Proof.
  iStartProof. iIntros "#Hjump #Hmemcpy".
  iPoseProof (memcpy_whole_public_correct (bv_unsigned base)
    (40 * Z.to_nat (bv_unsigned cursor)) bytes
    (Z_to_bv 64 (bv_unsigned base + 40 * bv_unsigned cursor))
    (sp + BV 64 1744)%bv (BV 64 40) (BV 64 0x15200)
    (accessCopyWholeFrame sp base cursor P) with "Hmemcpy") as "Hcallee".
  iEval (rewrite /IslaTraces.write_success_54.instrs.instr_map /=) in "Hjump".
  iDestruct "Hjump" as "#(H0 & H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8 & _)".
  zesu_run.
  Unshelve. all: prepare_sidecond.
  all: try assumption; try bv_solve.
Qed.
Print Assumptions access_copy_whole_correct.
