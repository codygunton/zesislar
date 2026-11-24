(* Adequacy with step budgets: a run whose charged code is proved from
   `step_budget budget` fetches at most `budget` charged instructions.

   `zesu_budget_adequacy` is `zesu_adequacy` (Export/Adequacy.v) with the
   charged set of the initial state and the budget the proof starts from.
   The two lemmas after it give a proof its code: the charged selected code
   of a table whose every address is charged, and `instr a None` at an
   address outside the table (a trap). *)
Require Import ZesuSsz.Automation2.All.
From iris.program_logic Require Import language.
From isla Require Import adequacy.
Require Import isla.riscv64.riscv64.

Lemma zesu_budget_adequacy Sigma `{!Arch} `{!islaPreG Sigma}
    (instrs : gmap addr isla_trace) (mem : mem_map) (regs : list reg_map)
    (Pks : spec) (charged : gset addr) (budget : nat) t2 sigma2 ks n :
  Pks [] ->
  (forall {HG : islaG Sigma},
    instr_table_raw instrs -∗ charged_set charged -∗
    step_budget (Z.of_nat budget) -∗
    backed_mem (dom mem) -∗ spec_trace Pks -∗
    ([∗ map] address ↦ value ∈ mem, bv_unsigned address ↦ₘ value)
    ={⊤}=∗
    [∗ list] registerMap ∈ regs, ∀ (_ : threadG),
      ([∗ map] register ↦ value ∈ registerMap, register ↦ᵣ value) -∗
      WPasm tnil) ->
  nsteps n
    (initial_local_state <$> regs,
      {| seq_instrs := instrs; seq_mem := mem; seq_charged := charged;
         seq_fetches := 0 |})
    ks (t2, sigma2) ->
  (forall thread, thread ∈ t2 -> not_stuck thread sigma2) /\ Pks ks /\
  (sigma2.(seq_fetches) <= budget)%nat.
Proof.
  intros Hempty Hwp.
  apply (isla_budget_adequacy Sigma instrs mem regs Pks charged budget t2 sigma2 ks n Hempty).
  intros HG. iIntros "Htable Hcharged Hcredits".
  iApply (Hwp with "Htable Hcharged [Hcredits]").
  by iApply step_budget_credits.
Qed.

(** The lookup of a table at an integer address. *)
Definition budget_table_lookup (instrs : gmap addr isla_trace) (address : Z) :
    option isla_trace :=
  match Z_to_bv_checked 64 address with
  | Some word => instrs !! word
  | None => None
  end.

Set Default Proof Using "Type".

Section code.
  Context `{!islaG Sigma} `{!threadG}.

  Lemma budget_charged_code instrs :
    instr_table_raw instrs -∗ charged_set (dom instrs) -∗
    instr_lookup_resources_charged (budget_table_lookup instrs).
  Proof.
    iIntros "#Htable #Hcharged". rewrite /instr_lookup_resources_charged.
    iIntros "!>" (address trace Hlookup).
    rewrite /budget_table_lookup in Hlookup.
    destruct (Z_to_bv_checked 64 address) as [word|] eqn:Hword; [|done].
    rewrite instr_charged_eq /instr_charged_def.
    iExists instrs, word, (dom instrs). iFrame "#". iPureIntro.
    split_and!; [done | done | by apply elem_of_dom].
  Qed.

  Lemma budget_table_gap instrs charged (address : bv 64) :
    instrs !! address = None -> address ∉ charged ->
    instr_table_raw instrs -∗ charged_set charged -∗
    instr (bv_unsigned address) None.
  Proof.
    iIntros (Hnone Huncharged) "#Htable #Hcharged".
    rewrite instr_eq /instr_def.
    iExists instrs, address, charged. iFrame "#". iPureIntro.
    split_and!; [by rewrite Z_to_bv_checked_bv_unsigned | done | done].
  Qed.
End code.

Print Assumptions zesu_budget_adequacy.
Print Assumptions budget_charged_code.
Print Assumptions budget_table_gap.
