(* A closed run with a step bound. Two charged instructions (the generated
   `addi sp, sp, -16` of `Generated/TestTraces/EntryAddi.v`, at 0x1000 and
   0x1004) and a trap at 0x1008, outside the table. Every run from the start
   state fetches at most two charged instructions. *)
Require Import ZesuMachineMap.Machine.
Require Import ZesuSsz.Export.Adequacy.
Require Import ZesuSsz.Export.BudgetAdequacy.
Require Import ZesuSsz.Generated.TestTraces.EntryAddi.
From Coq Require Import ZArith.ZArith Lists.List.
From iris.program_logic Require Import language.
From isla Require Import adequacy.
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Automation2.All.

Definition budget_example_instrs : gmap addr isla_trace :=
  <[BV 64 0x1000 := trace_entry_addi]> (<[BV 64 0x1004 := trace_entry_addi]> ∅).

Definition budget_example_regs (sp : bv 64) : reg_map :=
  <["PC" := RVal_Bits (BV 64 0x1000)]>
    (<["x2" := RVal_Bits sp]>
      (zesu_ram_sys_regs_map (BV 64 0) (BV 64 0) (BV 64 0) (BV 64 0))).

Definition budget_example_spec : spec :=
  scons (SInstrTrap (BV 64 0x1008)) snil.

Definition budget_example_code `{!islaG Sigma} `{!threadG} : iProp Sigma :=
  instr_lookup_resources_charged (budget_table_lookup budget_example_instrs).

Section block.
  Context `{!islaG Sigma} `{!threadG}.

  Lemma budget_example_block (sp : bv 64) :
    instr 0x1008 None -∗
    budget_example_code -∗
    instr_body 0x1000
      (reg_col zesu_sys_regs ∗ "x2" ↦ᵣ RVal_Bits sp ∗ step_budget 2 ∗
       spec_trace budget_example_spec ∗ True).
  Proof. zesu_block2. Qed.
End block.

Lemma budget_example_fetches (sp : bv 64) t2 sigma2 ks n :
  nsteps n
    (initial_local_state <$> [budget_example_regs sp],
      {| seq_instrs := budget_example_instrs; seq_mem := ∅;
         seq_charged := dom budget_example_instrs; seq_fetches := 0 |})
    ks (t2, sigma2) ->
  (forall thread, thread ∈ t2 -> not_stuck thread sigma2) /\
  budget_example_spec ks /\ (sigma2.(seq_fetches) <= 2)%nat.
Proof.
  intros Hsteps.
  set Sigma : gFunctors := #[islaΣ].
  apply: (@zesu_budget_adequacy Sigma riscv64_arch _ _ _ _ budget_example_spec _ 2
    _ _ _ _ _ _ Hsteps).
  { rewrite /budget_example_spec /scons. by left. }
  iIntros (?) "#Htable #Hcharged Hbudget _ Hspec _ /= !>".
  iSplitL; [|done]. iIntros (?) "Hregs".
  rewrite /budget_example_regs.
  do 2 (rewrite big_sepM_insert; [|by vm_compute]).
  iDestruct "Hregs" as "(HPC & Hx2 & Hsys)".
  iApply wp_asm_thread_ctx. iIntros (?) "Hctx".
  iMod (zesu_ram_sys_regs_init with "Hctx Hsys") as "[$ Hsys]"; [by vm_compute|].
  iModIntro.
  iApply (wp_next_instr_pre with "HPC [] [-]").
  - iApply (budget_example_block with "[] []").
    + iApply (budget_table_gap budget_example_instrs _ (BV 64 0x1008)
        with "Htable Hcharged"); [by vm_compute | by vm_compute].
    + iApply (budget_charged_code with "Htable Hcharged").
  - iFrame. done.
Qed.

Print Assumptions budget_example_block.
Print Assumptions budget_example_fetches.
