(* Step budgets: the instruction count a charged proof may still fetch.

   A function is charged when its selected code is
   `instr_lookup_resources_charged` (InstrSpecs/LookupCharged.v): each fetch
   of one of its instructions asks for `step_credits 1`. The contract states
   the credits it owns as `step_budget z`, a count in `Z` so that budgets are
   expressions over the contract's binders.

   Rules (all are Lithium instances; none redefines a hook):
   - Fetch. A goal `step_credits 1 ∗ G` takes one credit from the context's
     `step_budget z` (side condition `1 ≤ z`) and continues with `G` and
     `step_budget (z - 1)` in the context.
   - Budget request. A goal `step_budget z2 ∗ G` is served from the context's
     `step_budget z1` by `step_budget_split`: side conditions `0 ≤ z2` and
     `z2 ≤ z1`; the context keeps `step_budget (z1 - z2)`. The policy is one
     for every request: always split. A jump to a successor entry leaves
     the remainder unused and it is dropped at the block end (Iris is
     affine); a call keeps it for the return continuation, which is proved
     with the remainder in its context. An identical request
     (`z2` syntactically `z1`) is framed directly by Lithium and leaves
     nothing.
   - Remainders. `z - k` is computed to a literal when both are closed; a
     closed `k` subtracted from `z0 - k0` with closed `k0` folds to
     `z0 - (k0 + k)` computed (so `z - 1 - 1` is kept as `z - 2`);
     otherwise the remainder is `z - k`.
   - Selected code. A fetch at a closed address of a charged table reads the
     trace by VM evaluation of the lookup (InstrSpecs/LookupCharged.v,
     `charged_trace_at`); an address that is not closed is refused before
     evaluation. A charged instruction answers an `instr_pre` request (a call's
     return continuation) by `instr_pre_intro_charged`: the continuation pays
     the instruction out of its precondition and context. *)

From Coq Require Import ZArith.ZArith Lia.
Require Import isla.riscv64.riscv64.
Require Import InstrSpecs.LookupCharged.
Require Import ZesuSsz.Automation2.VmClosed.

Local Open Scope Z_scope.

Definition step_budget_def `{!islaG Sigma} (z : Z) : iProp Sigma :=
  (⌜0 <= z⌝ ∗ step_credits (Z.to_nat z))%I.
Definition step_budget_aux : seal (@step_budget_def). Proof. by eexists. Qed.
Definition step_budget `{!islaG Sigma} : Z -> iProp Sigma :=
  (step_budget_aux.(unseal)) Sigma _.
(* The one unfold point of `step_budget`. Lithium keeps it atomic: the rules
   below need it as one resource, so it has no `LithiumUnfold` instance. *)
Lemma step_budget_unseal `{!islaG Sigma} :
  @step_budget Sigma _ = @step_budget_def Sigma _.
Proof. rewrite /step_budget step_budget_aux.(seal_eq). done. Qed.
Global Typeclasses Opaque step_budget.

Set Default Proof Using "Type".

Section step_budget.
  Context `{!islaG Sigma}.

  Global Instance step_budget_timeless z : Timeless (step_budget (Sigma:=Sigma) z).
  Proof. rewrite step_budget_unseal /step_budget_def. apply _. Qed.

  Lemma step_budget_nonneg z : step_budget (Sigma:=Sigma) z ⊢ ⌜0 <= z⌝.
  Proof. rewrite step_budget_unseal /step_budget_def. iIntros "[$ _]". Qed.

  Lemma step_budget_split z1 z2 :
    0 <= z1 -> 0 <= z2 ->
    step_budget (Sigma:=Sigma) (z1 + z2) ⊣⊢ step_budget z1 ∗ step_budget z2.
  Proof.
    intros H1 H2. rewrite step_budget_unseal /step_budget_def.
    rewrite Z2Nat.inj_add // step_credits_split.
    iSplit.
    - iIntros "(_ & $ & $)". iPureIntro. lia.
    - iIntros "[(_ & $) (_ & $)]". iPureIntro. lia.
  Qed.

  Lemma step_budget_weaken z1 z2 :
    0 <= z2 <= z1 -> step_budget (Sigma:=Sigma) z1 ⊢ step_budget z2.
  Proof.
    intros Hz. rewrite (_ : z1 = z2 + (z1 - z2)); [|lia].
    rewrite step_budget_split; [|lia..]. iIntros "[$ _]".
  Qed.

  Lemma step_budget_spend z :
    1 <= z -> step_budget (Sigma:=Sigma) z ⊢ step_credits 1 ∗ step_budget (z - 1).
  Proof.
    intros Hz. rewrite {1}(_ : z = 1 + (z - 1)); [|lia].
    rewrite step_budget_split; [|lia..].
    rewrite {1}step_budget_unseal /step_budget_def. iIntros "[[_ $] $]".
  Qed.

  Lemma step_budget_credits n :
    step_credits n ⊢ step_budget (Sigma:=Sigma) (Z.of_nat n).
  Proof.
    rewrite step_budget_unseal /step_budget_def Nat2Z.id.
    iIntros "$". iPureIntro. lia.
  Qed.
End step_budget.

(** The remainder `z - k` of a budget, chosen by [zesu_budget_rest_apply]. *)
Definition zesu_budget_rest {Sigma : gFunctors} (z k : Z)
    (T : Z -> iProp Sigma) : iProp Sigma :=
  (∃ rest, ⌜rest = z - k⌝ ∗ T rest)%I.
Arguments zesu_budget_rest : simpl never.
Global Typeclasses Opaque zesu_budget_rest.

Program Definition zesu_budget_rest_hint {Sigma : gFunctors} (z k rest : Z) :
  rest = z - k -> LiTactic (zesu_budget_rest (Sigma:=Sigma) z k) :=
  fun H => {| li_tactic_P T := T rest |}.
Next Obligation.
  intros Sigma z k rest Hrest T. rewrite /zesu_budget_rest.
  iIntros "HT". iExists rest. iFrame. iPureIntro. exact Hrest.
Qed.

Ltac zesu_budget_rest_apply z k :=
  first [
    zesu_vm_closed (z - k)%Z;
    let rest := eval vm_compute in (z - k)%Z in
    apply (zesu_budget_rest_hint z k rest); vm_compute; reflexivity
  | lazymatch z with
    | (?base - ?k0)%Z =>
        zesu_vm_closed (k0 + k)%Z;
        let total := eval vm_compute in (k0 + k)%Z in
        apply (zesu_budget_rest_hint z k (base - total)%Z); lia
    end
  | apply (zesu_budget_rest_hint z k (z - k)%Z); reflexivity ].

Global Hint Extern 10 (LiTactic (zesu_budget_rest ?z ?k)) =>
  zesu_budget_rest_apply z k : typeclass_instances.

(** The trace of a charged table at a closed address. *)
Program Definition charged_trace_at_hint {Sigma : gFunctors}
    (lookup : Z -> option isla_trace) (address : Z) (trace : isla_trace) :
  lookup address = Some trace ->
  LiTactic (charged_trace_at (Sigma:=Sigma) lookup address) :=
  fun H => {| li_tactic_P T := T trace |}.
Next Obligation.
  intros Sigma lookup address trace Hlookup T. rewrite /charged_trace_at.
  iIntros "HT". iExists trace. iFrame. iPureIntro. exact Hlookup.
Qed.

Ltac zesu_charged_trace_apply lookup address :=
  zesu_vm_closed (lookup address);
  let result := eval vm_compute in (lookup address) in
  lazymatch result with
  | Some ?trace =>
      apply (charged_trace_at_hint lookup address trace); vm_compute; reflexivity
  end.

Global Hint Extern 10 (LiTactic (charged_trace_at ?lookup ?address)) =>
  zesu_charged_trace_apply lookup address : typeclass_instances.

Section rules.
  Context `{!islaG Sigma} `{!threadG}.

  Global Instance step_credits_related A (n : A -> nat) :
    RelatedTo (fun x : A => step_credits (n x)) :=
    {| rt_fic := FindDirect (fun z => step_budget (Sigma:=Sigma) z) |}.

  Global Instance step_budget_related A (z : A -> Z) :
    RelatedTo (fun x : A => step_budget (Sigma:=Sigma) (z x)) :=
    {| rt_fic := FindDirect (fun z => step_budget (Sigma:=Sigma) z) |}.

  Lemma subsume_step_budget_credit z G :
    (⌜1 <= z⌝ ∗ li_tactic (zesu_budget_rest z 1)
      (fun rest => step_budget rest -∗ G tt))
    ⊢ subsume (step_budget z) (fun _ : unit => step_credits 1) G.
  Proof.
    iIntros "[%Hz HG] Hbudget". rewrite /li_tactic /zesu_budget_rest.
    iDestruct "HG" as (rest ->) "HG".
    iDestruct (step_budget_spend with "Hbudget") as "[Hcredit Hrest]"; [done|].
    iExists tt. iFrame "Hcredit". iApply ("HG" with "Hrest").
  Qed.
  Definition subsume_step_budget_credit_inst := [instance subsume_step_budget_credit].
  Global Existing Instance subsume_step_budget_credit_inst.

  Lemma subsume_step_budget_split z1 z2 G :
    (⌜0 <= z2⌝ ∗ ⌜z2 <= z1⌝ ∗ li_tactic (zesu_budget_rest z1 z2)
      (fun rest => step_budget rest -∗ G tt))
    ⊢ subsume (step_budget z1) (fun _ : unit => step_budget z2) G.
  Proof.
    iIntros "(%H2 & %H12 & HG) Hbudget". rewrite /li_tactic /zesu_budget_rest.
    iDestruct "HG" as (rest ->) "HG".
    iAssert (step_budget z2 ∗ step_budget (z1 - z2))%I
      with "[Hbudget]" as "[Hrequested Hrest]".
    { rewrite -step_budget_split; [|lia..].
      by replace (z2 + (z1 - z2)) with z1 by lia. }
    iExists tt. iFrame "Hrequested". iApply ("HG" with "Hrest").
  Qed.
  Definition subsume_step_budget_split_inst := [instance subsume_step_budget_split].
  Global Existing Instance subsume_step_budget_split_inst.

  (* A charged instruction answers a requested `instr_pre` (a call's return
     continuation): the continuation pays its first instruction. The form
     follows `subsume_instr_some_pre` (Contracts/IslarisCode.v). *)
  Lemma subsume_instr_charged_pre A address trace requested_l requested G :
    (∃ x,
      (requested x -∗ step_credits 1 ∗
        (arch_pc_reg ↦ᵣ RVal_Bits (Z_to_bv 64 address) -∗ WPasm trace)) ∗
      G x)
    ⊢ subsume (instr_charged address trace)
        (fun x : A => instr_pre' (requested_l x) address (requested x)) G.
  Proof.
    iDestruct 1 as (x) "(Hwp & HG)".
    iIntros "Hinstr". iExists x. iFrame "HG".
    iApply (instr_pre_intro_charged with "Hinstr Hwp").
  Qed.
  Definition subsume_instr_charged_pre_inst := [instance subsume_instr_charged_pre].
  Global Existing Instance subsume_instr_charged_pre_inst | 20.
End rules.

Print Assumptions step_budget_split.
Print Assumptions step_budget_weaken.
Print Assumptions step_budget_spend.
Print Assumptions subsume_step_budget_credit.
Print Assumptions subsume_step_budget_split.
Print Assumptions subsume_instr_charged_pre.
