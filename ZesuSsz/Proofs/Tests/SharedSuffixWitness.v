Require Import ZesuSsz.Automation.All.
Require Import ZesuSsz.Automation.Sets.call.
Require Import ZesuSsz.Automation.SharedSuffixWitness.
Require Import ZesuSsz.Automation.SealedCoverage.
Require Import ZesuSsz.Automation.Switches.TracePrefixTail.
Require Import isla.riscv64.riscv64.

Definition sharedSuffixFacts (row candidate : list (bv 8))
    (rest prefix : list (list (bv 8))) : Prop :=
  True /\ row :: rest = prefix ++ candidate :: rest.


Definition sharedSuffixBundle `{!islaG Sigma} (row : list (bv 8))
    (rest prefix : list (list (bv 8))) (candidate : list (bv 8))
    (R : iProp Sigma) : iProp Sigma :=
  (R ∗ ⌜sharedSuffixFacts row candidate rest prefix⌝ ∗ True)%I.
Global Instance : LithiumUnfold (@sharedSuffixBundle) := I.
Global Typeclasses Opaque sharedSuffixBundle.

Lemma shared_suffix_preserves_arrays `{!islaG Sigma} `{!threadG}
    (base other : Z) (row unrelated : list (bv 8))
    (rest : list (list (bv 8))) :
  base ↦ₘ∗ (row ++ concat rest) -∗ other ↦ₘ∗ unrelated -∗
  (∃ y : li_prod (list (bv 8)) (li_prod (list (list (bv 8))) unit),
    ⌜row :: rest = y.2ₗ ++ y.1ₗ :: rest⌝ ∗
    base ↦ₘ∗ (row ++ concat rest) ∗ other ↦ₘ∗ unrelated ∗ True).
Proof.
  iIntros "Hsource Hunrelated". zesu_select_shared_suffix_tuple.
  iSplit; first (iPureIntro; reflexivity). iFrame.
Qed.

Lemma shared_suffix_registered_bundle `{!islaG Sigma}
    (row : list (bv 8)) (rest : list (list (bv 8))) (R : iProp Sigma) :
  R -∗ ∃ y : li_prod (list (bv 8)) (li_prod (list (list (bv 8))) unit),
    sharedSuffixBundle row rest y.2ₗ y.1ₗ R.
Proof.
  iIntros "HR". zesu_select_shared_suffix_tuple.
  rewrite /sharedSuffixBundle /sharedSuffixFacts. iFrame. iPureIntro. split; done.
Qed.

Lemma shared_suffix_rejects_missing `{!islaG Sigma} (row : list (bv 8)) :
  (∃ y : li_prod (list (bv 8)) (li_prod (list (list (bv 8))) unit),
     ⌜y.1ₗ = row⌝ : iProp Sigma) -∗
  (∃ y : li_prod (list (bv 8)) (li_prod (list (list (bv 8))) unit),
     ⌜y.1ₗ = row⌝ : iProp Sigma).
Proof. iIntros "H". tryif zesu_select_shared_suffix_tuple then fail "Accepted invalid tuple" else idtac. iExact "H". Qed.

Lemma shared_suffix_rejects_different `{!islaG Sigma}
    (row : list (bv 8)) (left right : list (list (bv 8))) :
  (∃ y : li_prod (list (bv 8)) (li_prod (list (list (bv 8))) unit),
     ⌜row :: left = y.2ₗ ++ y.1ₗ :: right⌝ : iProp Sigma) -∗
  (∃ y : li_prod (list (bv 8)) (li_prod (list (list (bv 8))) unit),
     ⌜row :: left = y.2ₗ ++ y.1ₗ :: right⌝ : iProp Sigma).
Proof. iIntros "H". tryif zesu_select_shared_suffix_tuple then fail "Accepted invalid tuple" else idtac. iExact "H". Qed.

Lemma shared_suffix_rejects_unrelated `{!islaG Sigma}
    (row unrelated : list (bv 8)) (rest : list (list (bv 8))) :
  (∃ y : li_prod (list (bv 8)) (li_prod (list (list (bv 8))) unit),
     ⌜row :: rest = y.2ₗ ++ unrelated :: rest⌝ : iProp Sigma) -∗
  (∃ y : li_prod (list (bv 8)) (li_prod (list (list (bv 8))) unit),
     ⌜row :: rest = y.2ₗ ++ unrelated :: rest⌝ : iProp Sigma).
Proof. iIntros "H". tryif zesu_select_shared_suffix_tuple then fail "Accepted invalid tuple" else idtac. iExact "H". Qed.

Lemma shared_suffix_rejects_evars (row : list (bv 8))
    (rest : list (list (bv 8))) : True.
Proof.
  pose (rm := ([] : list (bv 8))).
  pose (pm := ([] : list (list (bv 8)))).
  evar (unknown_row : list (bv 8)).
  let facts := constr:(unknown_row :: rest = pm ++ rm :: rest) in
  tryif zesu_shared_suffix_pure 12 facts rm pm ltac:(fun _ => idtac)
  then fail "Accepted unresolved tuple" else idtac.
  evar (unknown_suffix : list (list (bv 8))).
  let facts := constr:(row :: unknown_suffix = pm ++ rm :: unknown_suffix) in
  tryif zesu_shared_suffix_pure 12 facts rm pm ltac:(fun _ => idtac)
  then fail "Accepted unresolved tuple" else idtac.
  instantiate (unknown_row := []). instantiate (unknown_suffix := []). exact I.
Qed.
Print Assumptions shared_suffix_preserves_arrays.
Print Assumptions shared_suffix_registered_bundle.

Definition opaqueSharedSuffixFacts (row candidate : list (bv 8))
    (rest prefix : list (list (bv 8))) : Prop :=
  True /\ row :: rest = prefix ++ candidate :: rest.
Global Opaque opaqueSharedSuffixFacts.
Lemma shared_suffix_rejects_opaque `{!islaG Sigma}
    (row : list (bv 8)) (rest : list (list (bv 8))) :
  (∃ y : li_prod (list (bv 8)) (li_prod (list (list (bv 8))) unit),
    ⌜opaqueSharedSuffixFacts row y.1ₗ rest y.2ₗ⌝ : iProp Sigma) -∗
  (∃ y : li_prod (list (bv 8)) (li_prod (list (list (bv 8))) unit),
    ⌜opaqueSharedSuffixFacts row y.1ₗ rest y.2ₗ⌝ : iProp Sigma).
Proof.
  iIntros "H".
  tryif zesu_select_shared_suffix_tuple then fail "Accepted opaque facts" else idtac.
  iExact "H".
Qed.

Definition sharedSuffixSeal `{!islaG Sigma} (R : iProp Sigma) : iProp Sigma := R.
Global Typeclasses Opaque sharedSuffixSeal.
Lemma shared_suffix_preserves_primitives `{!islaG Sigma} `{!threadG}
    (row : list (bv 8)) (rest : list (list (bv 8)))
    (address pc : Z) (tail : spec) (R : iProp Sigma) :
  mmio_range address 16 -∗ spec_trace tail -∗ instr_pre pc R -∗
  sharedSuffixSeal R -∗
  (∃ y : li_prod (list (bv 8)) (li_prod (list (list (bv 8))) unit),
    mmio_range address 16 ∗ spec_trace tail ∗ instr_pre pc R ∗
    sharedSuffixSeal R ∗ ⌜row :: rest = y.2ₗ ++ y.1ₗ :: rest⌝ ∗ True).
Proof.
  iIntros "Hio Htrace Hpre Hseal". zesu_select_shared_suffix_tuple.
  iFrame. iPureIntro. split; done.
Qed.
Print Assumptions shared_suffix_preserves_primitives.

Definition protectedSuffix `{!islaG Sigma} (P : iProp Sigma) := P.
Global Instance : LithiumUnfold (@protectedSuffix) := I.
Global Typeclasses Opaque protectedSuffix.
Global Instance protectedSuffix_seal `{!islaG Sigma} (P : iProp Sigma) :
  ZesuSealed (protectedSuffix P) P [] [].
Proof. constructor; intros; done. Qed.
Ltac reject_suffix P row_marker prefix_marker :=
  tryif zesu_shared_suffix_equation 32 P row_marker prefix_marker ltac:(fun _ => idtac)
  then fail "Searched inside protected resource" else idtac.
Lemma protected_registered_seal `{!islaG Sigma}
 (row : list (bv 8)) (rest : list (list (bv 8))) :
 (∃ y : li_prod (list (bv 8)) (li_prod (list (list (bv 8))) unit),
   protectedSuffix (⌜row :: rest = y.2ₗ ++ y.1ₗ :: rest⌝ : iProp Sigma)) -∗
 (∃ y : li_prod (list (bv 8)) (li_prod (list (list (bv 8))) unit),
   protectedSuffix (⌜row :: rest = y.2ₗ ++ y.1ₗ :: rest⌝ : iProp Sigma)).
Proof.
 iIntros "H".
 tryif zesu_select_shared_suffix_tuple then fail "Searched inside declared seal" else idtac.
 iExact "H".
Qed.
Lemma protected_primitive_heads `{!islaG Sigma} `{!threadG}
 (base : Z) (bytes row : list (bv 8)) (prefix : list (list (bv 8))) : True.
Proof.
 let P := constr:((base ↦ₘ∗ bytes)%I) in reject_suffix P row prefix.
 let P := constr:((base ↦ₘ (BV 8 1))%I) in reject_suffix P row prefix.
 let P := constr:((base ↦ₘ? 64)%I) in reject_suffix P row prefix.
 let P := constr:(reg_col sys_regs) in reject_suffix P row prefix.
 exact I.
Qed.
Print Assumptions protected_registered_seal.
Print Assumptions protected_primitive_heads.
