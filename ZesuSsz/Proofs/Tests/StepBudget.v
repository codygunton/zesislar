(* Step budgets (Automation2/StepBudget.v) on charged code.

   The program repeats the generated trace of `addi sp, sp, -16` (selected-ELF
   instruction 800d6960, `Generated/TestTraces/EntryAddi.v`); the trace reads
   the program counter, so it runs at any address. Every address of the table
   is charged: each fetch costs one credit. *)
From Coq Require Import ZArith.ZArith Lists.List.
Require Import isla.riscv64.riscv64.
Require Import ZesuMachineMap.Machine.
Require Import ZesuSsz.Contracts.SelectedCodeLookup.
Require Import ZesuSsz.Generated.TestTraces.EntryAddi.
Require Import ZesuSsz.Automation2.All.
Local Open Scope Z_scope.

(* Straight line: 0x1000, 0x1004, 0x1008. Call shape: the call instruction at
   0x1000, its return continuation at 0x2000 and 0x2004. *)
Definition step_budget_test_map : list (Z * isla_trace) :=
  [(0x1000, trace_entry_addi); (0x1004, trace_entry_addi);
   (0x1008, trace_entry_addi); (0x2000, trace_entry_addi);
   (0x2004, trace_entry_addi)].

Definition step_budget_test_code `{!islaG Sigma} `{!threadG} : iProp Sigma :=
  instr_lookup_resources_charged (selectedCodeLookup step_budget_test_map).
Global Instance : LithiumUnfold (@step_budget_test_code) := I.
Global Typeclasses Opaque step_budget_test_code.
(* The proofs read the table through the wrapper, as generated callers do. *)
#[local] Typeclasses Transparent step_budget_test_code.

Section tests.
  Context `{!islaG Sigma} `{!threadG}.

  (* Three charged instructions with three credits. *)
  Lemma step_budget_three_closes (sp : bv 64) :
    instr_pre 0x100c (reg_col zesu_sys_regs ∗ "x2" ↦ᵣ: (fun _ => True) ∗ True) -∗
    step_budget_test_code -∗
    instr_body 0x1000
      (reg_col zesu_sys_regs ∗ "x2" ↦ᵣ RVal_Bits sp ∗ step_budget 3 ∗ True).
  Proof. zesu_block2. Qed.

  (* Two credits do not pay for the third fetch. *)
  Lemma step_budget_two_fails : True.
  Proof.
    Fail assert (forall sp : bv 64,
      ⊢ instr_pre 0x100c (reg_col zesu_sys_regs ∗ "x2" ↦ᵣ: (fun _ => True) ∗ True) -∗
        step_budget_test_code -∗
        instr_body 0x1000
          (reg_col zesu_sys_regs ∗ "x2" ↦ᵣ RVal_Bits sp ∗ step_budget 2 ∗ True))
      by (intros sp; solve [zesu_block2]).
    exact I.
  Qed.

  (* Two blocks. Block A (0x1000, 0x1004) owns three credits, spends two and
     jumps to block B's entry, which asks for one. *)
  Lemma step_budget_block_a (sp : bv 64) :
    instr_pre 0x1008
      (reg_col zesu_sys_regs ∗ "x2" ↦ᵣ: (fun _ => True) ∗ step_budget 1 ∗ True) -∗
    step_budget_test_code -∗
    instr_body 0x1000
      (reg_col zesu_sys_regs ∗ "x2" ↦ᵣ RVal_Bits sp ∗ step_budget 3 ∗ True).
  Proof. zesu_block2. Qed.

  (* Block B pays its one instruction out of its entry. *)
  Lemma step_budget_block_b :
    instr_pre 0x100c (reg_col zesu_sys_regs ∗ "x2" ↦ᵣ: (fun _ => True) ∗ True) -∗
    step_budget_test_code -∗
    instr_body 0x1008
      (reg_col zesu_sys_regs ∗ "x2" ↦ᵣ: (fun _ => True) ∗ step_budget 1 ∗ True).
  Proof. zesu_block2. Qed.

  (* A symbolic budget: the fetches leave `z - 3`, folded from `z - 1 - 1 - 1`,
     and the successor asks for exactly that. *)
  Lemma step_budget_symbolic (sp : bv 64) (z : Z) :
    instr_pre 0x100c
      (reg_col zesu_sys_regs ∗ "x2" ↦ᵣ: (fun _ => True) ∗ step_budget (z - 3) ∗ True) -∗
    step_budget_test_code -∗
    instr_body 0x1000
      (reg_col zesu_sys_regs ∗ "x2" ↦ᵣ RVal_Bits sp ∗ ⌜3 <= z⌝ ∗ step_budget z ∗ True).
  Proof. zesu_block2. Qed.

  (* Call shape, as the block generator renders it: the return address is a
     block entry of its own. The call instruction (0x1000) costs one credit;
     the callee at 0x1004 takes five and returns to 0x2000. The return
     block's entry asks for the two credits that the call site kept; its two
     instructions spend them. *)
  Definition step_budget_test_callee (returned : iProp Sigma) : iProp Sigma :=
    instr_pre 0x1004
      (reg_col zesu_sys_regs ∗ "x2" ↦ᵣ: (fun _ => True) ∗ step_budget 5 ∗
       instr_pre 0x2000 returned ∗ True).

  Definition step_budget_test_return_entry : iProp Sigma :=
    reg_col zesu_sys_regs ∗ "x2" ↦ᵣ: (fun _ => True) ∗ step_budget 2 ∗ True.
End tests.
Global Instance : LithiumUnfold (@step_budget_test_callee) := I.
Global Instance : LithiumUnfold (@step_budget_test_return_entry) := I.
Global Typeclasses Opaque step_budget_test_callee step_budget_test_return_entry.

Section call_tests.
  Context `{!islaG Sigma} `{!threadG}.

  Lemma step_budget_call_site (sp : bv 64) :
    step_budget_test_callee
      (reg_col zesu_sys_regs ∗ "x2" ↦ᵣ: (fun _ => True) ∗ True) -∗
    instr_pre 0x2000 step_budget_test_return_entry -∗
    step_budget_test_code -∗
    instr_body 0x1000
      (reg_col zesu_sys_regs ∗ "x2" ↦ᵣ RVal_Bits sp ∗ step_budget 8 ∗ True).
  Proof.
    rewrite /step_budget_test_callee /step_budget_test_return_entry. zesu_block2.
  Qed.

  Lemma step_budget_call_return :
    instr_pre 0x2008 (reg_col zesu_sys_regs ∗ "x2" ↦ᵣ: (fun _ => True) ∗ True) -∗
    step_budget_test_code -∗
    instr_body 0x2000 step_budget_test_return_entry.
  Proof. rewrite /step_budget_test_return_entry. zesu_block2. Qed.

  (* Seven credits do not pay for the call, the callee and the return block. *)
  Lemma step_budget_call_site_short : True.
  Proof.
    Fail assert (forall sp : bv 64,
      ⊢ step_budget_test_callee
          (reg_col zesu_sys_regs ∗ "x2" ↦ᵣ: (fun _ => True) ∗ True) -∗
        instr_pre 0x2000 step_budget_test_return_entry -∗
        step_budget_test_code -∗
        instr_body 0x1000
          (reg_col zesu_sys_regs ∗ "x2" ↦ᵣ RVal_Bits sp ∗ step_budget 7 ∗ True))
      by (intros sp; rewrite /step_budget_test_callee /step_budget_test_return_entry;
          solve [zesu_block2]).
    exact I.
  Qed.
End call_tests.

Print Assumptions step_budget_three_closes.
Print Assumptions step_budget_block_a.
Print Assumptions step_budget_block_b.
Print Assumptions step_budget_symbolic.
Print Assumptions step_budget_call_site.
Print Assumptions step_budget_call_return.
