Require Import isla.riscv64.riscv64.
Require ZesuSsz.Automation2.All.
Require Import ZesuSsz.Contracts.NamedEquation.
Require Import ZesuSsz.Automation.All.

(* A named equation the block must establish, with no hypothesis of that name,
   is an ordinary equation (Lithium alone shelves the marker). *)
Lemma named_equation_goal_as_equation `{!islaG Sigma} `{!threadG}
    (name base : bv 64) (Hname : name = bv_add base (BV 64 8)) :
  ⊢@{iProp Sigma} ⌜zesu_named_eq name (bv_add base (BV 64 8))⌝ ∗ ⌜True⌝.
Proof.
  iStartProof.
  ZesuSsz.Automation2.Hooks.zesu_liAStep.
  lazymatch goal with
  | |- environments.envs_entails _ (⌜name = bv_add base (BV 64 8)⌝ ∗ _)%I => idtac
  end.
  iSplit; iPureIntro; [exact Hname | exact I].
Qed.
Print Assumptions named_equation_goal_as_equation.

(* With a hypothesis of the same value, the successor's binder takes the
   block's name. *)
Lemma named_equation_goal_from_hypothesis `{!islaG Sigma} `{!threadG}
    (name base : bv 64) (named : zesu_named_eq name (bv_add base (BV 64 8))) :
  exists successor : bv 64, ⊢@{iProp Sigma}
    ⌜zesu_named_eq successor (bv_add base (BV 64 8))⌝ ∗ ⌜successor = name⌝.
Proof.
  eexists. iStartProof.
  ZesuSsz.Automation2.Hooks.zesu_liAStep.
  lazymatch goal with
  | |- environments.envs_entails _ ⌜name = name⌝%I => idtac
  end.
  iPureIntro. reflexivity.
Qed.
Print Assumptions named_equation_goal_from_hypothesis.

(* The finisher sees the value of a name its goal mentions. *)
Lemma named_equation_opened_by_finish (name base : bv 64)
    (named : zesu_named_eq name (bv_add base (BV 64 8))) :
  name = bv_add base (BV 64 8).
Proof. ZesuSsz.Automation2.Finish.zesu_finish_base. Qed.
Print Assumptions named_equation_opened_by_finish.

(* Only the names the goal mentions, or the opened values mention, open. *)
Lemma named_equation_opens_mentioned_names (name middle other base : bv 64)
    (named : zesu_named_eq name (bv_add middle (BV 64 8)))
    (chained : zesu_named_eq middle (bv_add base (BV 64 8)))
    (unrelated : zesu_named_eq other base) :
  bv_unsigned name = bv_unsigned name.
Proof.
  ZesuSsz.Automation2.NamedEquations.zesu_open_named_equations.
  lazymatch type of named with _ = _ => idtac end.
  lazymatch type of chained with _ = _ => idtac end.
  lazymatch type of unrelated with zesu_named_eq _ _ => idtac end.
  reflexivity.
Qed.
Print Assumptions named_equation_opens_mentioned_names.

(* A load whose address mentions a local alias sees the alias's body; the
   step refuses an address with no alias. *)
Lemma named_equation_load_through_alias `{!islaG Sigma} `{!threadG}
    (pointer : bv 64) (bytes : list (bv 8))
    (Hlow : 400 <= bv_unsigned pointer) (Hhigh : bv_unsigned pointer < 2 ^ 63)
    (Hlength : length bytes = 40%nat) :
  ⊢@{iProp Sigma} (bv_unsigned pointer - 400 + 280) ↦ₘ∗ bytes -∗
    find_in_context (FindMemMapsTo (bv_unsigned
      (pointer + BV 64 18446744073709551216 + BV 64 400 + BV 64 18446744073709551528)%bv))
      (fun _ => True)%I.
Proof.
  iStartProof. iIntros "H".
  Fail ZesuSsz.Automation2.NamedEquations.zesu_unfold_let_mem_address.
  pose (alias := (pointer + BV 64 18446744073709551216 + BV 64 400 +
    BV 64 18446744073709551528)%bv).
  change (FindMemMapsTo (bv_unsigned (pointer + BV 64 18446744073709551216 +
    BV 64 400 + BV 64 18446744073709551528)%bv))
    with (FindMemMapsTo (bv_unsigned alias)).
  ZesuSsz.Automation2.NamedEquations.zesu_unfold_let_mem_address.
  lazymatch goal with
  | _ := _ : bv 64 |- _ => fail "the alias is kept"
  | |- environments.envs_entails _ (find_in_context (FindMemMapsTo (bv_unsigned
      (pointer + _ + _ + _)%bv)) _) => idtac
  end.
  repeat ZesuSsz.Automation2.Hooks.zesu_liAStep.
Qed.
Print Assumptions named_equation_load_through_alias.

(* In a block with a named equation (a call boundary), a successor's binder
   named like a block variable of the same type takes that variable, also
   after an unnamed binder opened a Lithium tuple; a binder with no namesake
   is left to Lithium. *)
Lemma named_binder_takes_block_variable `{!islaG Sigma} `{!threadG}
    (kept base : bv 64) (outcome : list nat) (named : zesu_named_eq kept base) :
  ⊢@{iProp Sigma} ∃ (kept : bv 64) (fresh_value : bv 64) (outcome : list nat),
    ⌜kept = fresh_value⌝ ∗ ⌜outcome = outcome⌝.
Proof.
  iStartProof.
  ZesuSsz.Automation2.Hooks.zesu_liAStep.
  lazymatch goal with
  | |- environments.envs_entails _ (∃ fresh_value : bv 64, _)%I => idtac
  end.
  Fail ZesuSsz.Automation2.NamedEquations.zesu_named_binder_witness.
  ZesuSsz.Automation2.Hooks.zesu_liAStep.
  ZesuSsz.Automation2.Hooks.zesu_liAStep.
  lazymatch goal with
  | |- environments.envs_entails _ (∃ _ : li_prod (bv 64) unit,
      ⌜kept = _⌝ ∗ ⌜outcome = outcome⌝)%I => idtac
  end.
  iExists (kept, tt)ₗ. iSplit; iPureIntro; reflexivity.
Qed.
Print Assumptions named_binder_takes_block_variable.

(* The same for an existential package framed with the rest of the goal. *)
Lemma named_binder_in_framed_package `{!islaG Sigma} `{!threadG}
    (kept base : bv 64) (named : zesu_named_eq kept base) (rest : iProp Sigma) :
  rest ⊢ (∃ kept : bv 64, ⌜kept = kept⌝) ∗ rest.
Proof.
  iStartProof. iIntros "Hrest".
  ZesuSsz.Automation2.NamedEquations.zesu_named_binder_witness.
  lazymatch goal with
  | |- environments.envs_entails _ (⌜kept = kept⌝ ∗ rest)%I => idtac
  end.
  iFrame. iPureIntro. reflexivity.
Qed.
Print Assumptions named_binder_in_framed_package.

(* A framed package whose first binder has no namesake: Lithium opens its
   tuple, and the later binder, still framed with the rest of the goal, takes
   the block variable of its name before liSep moves it out under another
   name. *)
Lemma named_binder_after_tuple_in_framed_package `{!islaG Sigma} `{!threadG}
    (kept base : bv 64) (named : zesu_named_eq kept base) (rest : iProp Sigma) :
  rest ⊢ (∃ (fresh_value : bv 64) (kept : bv 64), ⌜fresh_value = kept⌝ ∗ ⌜kept = kept⌝) ∗ rest.
Proof.
  iStartProof. iIntros "Hrest".
  Fail ZesuSsz.Automation2.NamedEquations.zesu_named_binder_witness.
  ZesuSsz.Automation2.Hooks.zesu_liAStep.
  ZesuSsz.Automation2.Hooks.zesu_liAStep.
  lazymatch goal with
  | |- environments.envs_entails _ (∃ _ : li_prod (bv 64) unit,
      (∃ kept : bv 64, _) ∗ rest)%I => idtac
  end.
  ZesuSsz.Automation2.NamedEquations.zesu_named_binder_witness.
  lazymatch goal with
  | |- environments.envs_entails _ (∃ _ : li_prod (bv 64) unit,
      (⌜_ = kept⌝ ∗ ⌜kept = kept⌝) ∗ rest)%I => idtac
  end.
  iExists (kept, tt)ₗ. iFrame "Hrest". iSplit; iPureIntro; reflexivity.
Qed.
Print Assumptions named_binder_after_tuple_in_framed_package.

(* A block with no named equation names its variables per block: the
   successor's binder of the same name is another value, so the binder step
   leaves it to Lithium. *)
Lemma named_binder_needs_named_equation `{!islaG Sigma} `{!threadG}
    (kept : bv 64) (rest : iProp Sigma) :
  rest ⊢ (∃ kept : bv 64, ⌜kept = kept⌝) ∗ rest.
Proof.
  iStartProof. iIntros "Hrest".
  Fail ZesuSsz.Automation2.NamedEquations.zesu_named_binder_witness.
  iSplitR "Hrest"; [iExists kept; iPureIntro; reflexivity | iExact "Hrest"].
Qed.
Print Assumptions named_binder_needs_named_equation.

(* Two calls' facts each bound a callee binder `before`; Rocq renamed the
   second `before0`. A later call's binder `before` is a third value, so the
   binder step leaves it to Lithium, even in a block with a named equation.
   A digit-final name gives no such evidence: `kept1` next to `kept13` still
   takes its namesake. *)
Lemma named_binder_skips_reused_name `{!islaG Sigma} `{!threadG}
    (kept base : bv 64) (named : zesu_named_eq kept base)
    (before before0 : list nat) (rest : iProp Sigma) :
  rest ⊢ (∃ before : list nat, ⌜before = before⌝) ∗ rest.
Proof.
  iStartProof. iIntros "Hrest".
  Fail ZesuSsz.Automation2.NamedEquations.zesu_named_binder_witness.
  iSplitR "Hrest"; [iExists before; iPureIntro; reflexivity | iExact "Hrest"].
Qed.
Print Assumptions named_binder_skips_reused_name.

Lemma named_binder_digit_final_name `{!islaG Sigma} `{!threadG}
    (kept1 kept13 base : bv 64) (named : zesu_named_eq kept1 base) (rest : iProp Sigma) :
  rest ⊢ (∃ kept1 : bv 64, ⌜kept1 = kept1⌝) ∗ rest.
Proof.
  iStartProof. iIntros "Hrest".
  ZesuSsz.Automation2.NamedEquations.zesu_named_binder_witness.
  lazymatch goal with
  | |- environments.envs_entails _ (⌜kept1 = kept1⌝ ∗ rest)%I => idtac
  end.
  iFrame. iPureIntro. reflexivity.
Qed.
Print Assumptions named_binder_digit_final_name.

(* A call's precondition restated over fresh binders, one of them named
   like an unrelated block variable: the stepping loop closes it from the
   call's facts, not from the names. *)
Lemma call_precondition_from_call_facts
    (domain : bv 64 → list nat → Prop) (meaning : bv 64 → list nat → nat → Prop)
    (x13 : bv 64) (before before0 : list nat) (after : nat)
    (Hother : domain x13 before) (Hdomain : domain x13 before0)
    (Hmeaning : meaning x13 before0 after) :
  ∃ (x13 : bv 64) (before : list nat), domain x13 before ∧ meaning x13 before after.
Proof. ZesuSsz.Automation2.Hooks.zesu_liAStep. Qed.
Print Assumptions call_precondition_from_call_facts.

(* The step unfolds an address alias before Lithium's lookup runs: liStep
   never sees a memory lookup whose address mentions a local alias. *)
#[local] Ltac liStep ::=
  lazymatch goal with
  | alias := _ |- environments.envs_entails _ (find_in_context (FindMemMapsTo ?address) _) =>
      lazymatch address with context [alias] => fail "liStep saw the alias" end
  | _ => idtac
  end;
  first [liExtensible | liSep | liAnd | liWand | liExist | liImpl | liForall |
    liSideCond | liFindInContext | liCase | liTrace | liTactic | liPersistent |
    liTrue | liFalse | liAccu | liDoneEvar | liUnfoldLetGoal].

Lemma named_equation_alias_before_lookup `{!islaG Sigma} `{!threadG}
    (pointer : bv 64) (bytes : list (bv 8))
    (Hlow : 400 <= bv_unsigned pointer) (Hhigh : bv_unsigned pointer < 2 ^ 63)
    (Hlength : length bytes = 40%nat) :
  ⊢@{iProp Sigma} (bv_unsigned pointer - 400 + 280) ↦ₘ∗ bytes -∗
    find_in_context (FindMemMapsTo (bv_unsigned
      (pointer + BV 64 18446744073709551216 + BV 64 400 + BV 64 18446744073709551528)%bv))
      (fun _ => True)%I.
Proof.
  iStartProof. iIntros "H".
  pose (alias := (pointer + BV 64 18446744073709551216 + BV 64 400 +
    BV 64 18446744073709551528)%bv).
  change (FindMemMapsTo (bv_unsigned (pointer + BV 64 18446744073709551216 +
    BV 64 400 + BV 64 18446744073709551528)%bv))
    with (FindMemMapsTo (bv_unsigned alias)).
  repeat ZesuSsz.Automation2.Hooks.zesu_liAStep.
Qed.
Print Assumptions named_equation_alias_before_lookup.
