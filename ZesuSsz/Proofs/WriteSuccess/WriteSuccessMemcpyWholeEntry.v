Require Import ZesuSsz.Automation.All.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessMemcpyWholeLoopClosed.
From Coq Require Import Lists.List ZArith.ZArith.
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Contracts.IslarisMachine.
From IslaTraces.write_success_02 Require Import instrs.
Local Open Scope Z_scope.

Definition memcpyWholeEntry `{!islaG Sigma} `{!threadG}
    (base : Z) (start : nat) (source : list (bv 8))
    (src dst n ret : bv 64) (P : iProp Sigma) : iProp Sigma :=
  (∃ (i tmp13 tmp14 : bv 64) (data : list (bv 8)),
   reg_col zesu_ram_sys_regs ∗ "x1" ↦ᵣ RVal_Bits ret ∗
   "x10" ↦ᵣ RVal_Bits dst ∗ "x11" ↦ᵣ RVal_Bits src ∗
   "x12" ↦ᵣ RVal_Bits n ∗ "x13" ↦ᵣ RVal_Bits tmp13 ∗
   "x14" ↦ᵣ RVal_Bits tmp14 ∗ "x15" ↦ᵣ RVal_Bits i ∗
   base ↦ₘ∗ source ∗ bv_unsigned dst ↦ₘ∗ data ∗
   ⌜bv_unsigned src = (base + Z.of_nat start)%Z⌝ ∗
   ⌜bv_unsigned n = Z.of_nat (length data)⌝ ∗
   ⌜(start + length data <= length source)%nat⌝ ∗
   ⌜(0x20000000 <= base)%Z⌝ ∗ ⌜(base + Z.of_nat (length source) < 0x40000000)%Z⌝ ∗
   ⌜(0x20000000 <= bv_unsigned dst)%Z⌝ ∗ ⌜(bv_unsigned dst + bv_unsigned n < 0x40000000)%Z⌝ ∗
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
Global Instance : LithiumUnfold (@memcpyWholeEntry) := I.


Lemma memcpy_whole_entry_correct `{!islaG Sigma} `{!threadG}
    base start source src dst n ret (P : iProp Sigma) :
  ([∗ list] instruction ∈ IslaTraces.write_success_02.instrs.instr_map,
    instr instruction.1 (Some instruction.2))%I -∗
  instr_body 0x101d4 (memcpyWholeEntry base start source src dst n ret P).
Proof.
  iStartProof. iIntros "#Hcode".
  iPoseProof (memcpy_whole_loop_closed base start source src dst n ret P
    with "Hcode") as "#Hloop".
  iEval (rewrite /instr_map /=) in "Hcode".
  iDestruct "Hcode" as "#(H0 & H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8 & _)".
  zesu_run.
  Unshelve. all: prepare_sidecond.
  all: try assumption; try bv_solve.
Qed.
Print Assumptions memcpy_whole_entry_correct.
