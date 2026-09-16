Require Import ZesuSsz.Automation.AllLegacy.
Require Import ZesuMachineMap.Machine.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessMemcpyWholeEntry.
Require Import ZesuSsz.Contracts.IslarisMemory.
From Coq Require Import Lists.List ZArith.ZArith.
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Contracts.IslarisMachine.
From IslaTraces.write_success_02 Require Import instrs.
Local Open Scope Z_scope.

Definition memcpyWholePublic `{!islaG Sigma} `{!threadG}
    (base : Z) (start : nat) (source : list (bv 8))
    (src dst n ret : bv 64) (P : iProp Sigma) : iProp Sigma :=
  (∃ (i tmp13 tmp14 : bv 64),
   reg_col zesu_ram_sys_regs ∗ "x1" ↦ᵣ RVal_Bits ret ∗
   "x10" ↦ᵣ RVal_Bits dst ∗ "x11" ↦ᵣ RVal_Bits src ∗
   "x12" ↦ᵣ RVal_Bits n ∗ "x13" ↦ᵣ RVal_Bits tmp13 ∗
   "x14" ↦ᵣ RVal_Bits tmp14 ∗ "x15" ↦ᵣ RVal_Bits i ∗
   base ↦ₘ∗ source ∗ bv_unsigned dst ↦ₘ? bv_unsigned n ∗
   ⌜bv_unsigned src = (base + Z.of_nat start)%Z⌝ ∗
   ⌜(start + Z.to_nat (bv_unsigned n) <= length source)%nat⌝ ∗
   ⌜((mapRamBase defaultMap) <= base)%Z⌝ ∗ ⌜(base + Z.of_nat (length source) < (machineRamEnd defaultMap))%Z⌝ ∗
   ⌜((mapRamBase defaultMap) <= bv_unsigned dst)%Z⌝ ∗ ⌜(bv_unsigned dst + bv_unsigned n < (machineRamEnd defaultMap))%Z⌝ ∗
   ⌜bv_extract 0 1 ret = BV 1 0⌝ ∗ ⌜bv_extract 1 1 ret = BV 1 0⌝ ∗
   ⌜bv_extract 0 2 ret = BV 2 0⌝ ∗
   instr_pre (bv_unsigned ret)
     (∃ final13 final14 : bv 64,
      reg_col zesu_ram_sys_regs ∗ "x1" ↦ᵣ RVal_Bits ret ∗
      "x10" ↦ᵣ RVal_Bits dst ∗ "x11" ↦ᵣ RVal_Bits src ∗
      "x12" ↦ᵣ RVal_Bits n ∗ "x13" ↦ᵣ RVal_Bits final13 ∗
      "x14" ↦ᵣ RVal_Bits final14 ∗ "x15" ↦ᵣ RVal_Bits n ∗
      base ↦ₘ∗ source ∗ bv_unsigned dst ↦ₘ∗ take (Z.to_nat (bv_unsigned n)) (drop start source) ∗
      P ∗ True) ∗ P ∗ True)%I.
Global Instance : LithiumUnfold (@memcpyWholePublic) := I.



Lemma memcpy_whole_public_correct `{!islaG Sigma} `{!threadG}
    base start source src dst n ret (P : iProp Sigma) :
  ([∗ list] instruction ∈ IslaTraces.write_success_02.instrs.instr_map,
    instr instruction.1 (Some instruction.2))%I -∗
  instr_body 0x101d4 (memcpyWholePublic base start source src dst n ret P).
Proof.
  iStartProof. iIntros "#Hcode".
  iEval (rewrite instr_pre'_eq). iIntros "Hspec".
  iDestruct "Hspec" as (i tmp13 tmp14)
    "(Hsys & H1 & H10 & H11 & H12 & H13 & H14 & H15 & Hsrc & Hdst &
      %Hcursor & %Hbound & %Hlow & %Hhigh & %Hdstlow & %Hdsthigh &
      %Hret0 & %Hret1 & %Hret2 & Hret & HP & _)".
  iDestruct (mem_mapsto_uninit_to_byte_array with "Hdst") as (data Hsize) "Hdst".
  have Hnsize : bv_unsigned n = Z.of_nat (length data) by lia.
  have Hwhole : (start + length data <= length source)%nat.
  { rewrite Hnsize Nat2Z.id in Hbound. exact Hbound. }
  iPoseProof (memcpy_whole_entry_correct base start source src dst n ret P
    with "Hcode") as "Hbody".
  iEval (rewrite instr_pre'_eq) in "Hbody".
  iApply ("Hbody" with "[-]").
  iExists i, tmp13, tmp14, data. iFrame.
  repeat iSplit; try iPureIntro; try assumption.
Qed.
Print Assumptions memcpy_whole_public_correct.

Lemma memcpy_whole_public_pre `{!islaG Sigma} `{!threadG}
    base start source src dst n ret (P : iProp Sigma) :
  ([∗ list] instruction ∈ IslaTraces.write_success_02.instrs.instr_map,
    instr instruction.1 (Some instruction.2))%I -∗
  □ instr_pre 0x101d4 (memcpyWholePublic base start source src dst n ret P).
Proof.
  iIntros "#Hcode". iModIntro. iApply instr_pre_to_body. iNext.
  iApply (memcpy_whole_public_correct with "Hcode").
Qed.
Print Assumptions memcpy_whole_public_pre.
