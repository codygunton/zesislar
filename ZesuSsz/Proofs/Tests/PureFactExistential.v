Require Import ZesuSsz.Automation.All.
Require Import ZesuSsz.Compliance.DecodeItemUnfoldRegistrations.
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Contracts.RlpDecodeItem.
Require Import ZesuSsz.Contracts.RlpDecodeItemContract.
Require Import ZesuSsz.Contracts.RlpDecodeItemByteFold.
Require Import ZesuSsz.Compliance.DecodeItemCorrectedWitnessSelections.
From Ltac2 Require Import Ltac2.
Set Default Proof Mode "Classic".
Import iris.proofmode.environments.
Open Scope Z_scope.

Require Import ZesuSsz.Automation.Switches.PureFactHints.

Ltac pure_fact_existential_bind_environment :=
  lazymatch goal with
  | |- envs_entails ?environment ?target =>
      pose (IPM_TEST_ALIAS := environment);
      change (envs_entails IPM_TEST_ALIAS target)
  end.

Lemma pure_fact_existential_off `{!islaG Sigma}
    args n i payloadStart lengthBytes (n2 : bv 8) (result : iProp Sigma) :
  decodeItemByteFoldFacts args n i payloadStart lengthBytes ->
  @ZesuPureFactIntro Sigma
    (∃ index : nat, ⌜Z.of_nat index =
      (payloadStart + i + 0 - decodeItemInputPointer args) `div` 1⌝ ∗
      ⌜(index < length (decodeItemInputBytes args))%nat⌝ ∗
      ∃ Heq : 8%N = 8%N, ∀ vmem : bv 8,
        ⌜decodeItemInputBytes args !! index = Some vmem⌝ -∗
        ⌜eq_rect 8%N bv n2 8%N Heq = vmem⌝ -∗
        decodeItemInputPointer args ↦ₘ∗ decodeItemInputBytes args -∗ result)%I
    (⌜decodeItemByteFoldFacts args n i payloadStart lengthBytes⌝ ∗
      ⌜(Z.to_nat (1 + i)%Z < length (decodeItemInputBytes args))%nat⌝ ∗
      ∃ Heq : 8%N = 8%N, ∀ vmem : bv 8,
        ⌜decodeItemInputBytes args !! Z.to_nat (1 + i)%Z = Some vmem⌝ -∗
        ⌜eq_rect 8%N bv n2 8%N Heq = vmem⌝ -∗
        decodeItemInputPointer args ↦ₘ∗ decodeItemInputBytes args -∗ result)%I.
Proof.
  intros Hfold. unfold ZesuPureFactIntro. iIntros "Hsource". pure_fact_existential_bind_environment.
  Fail zesu_pure_fact_existential_if_enabled.
  unfold IPM_TEST_ALIAS.
  iApply (@zesu_pure_fact_intro _ _ _ (@decodeItemFoldArrayIndexWitness Sigma islaG0 args n i payloadStart lengthBytes
    (fun index => (⌜(index < length (decodeItemInputBytes args))%nat⌝ ∗
      ∃ Heq : 8%N = 8%N, ∀ vmem : bv 8,
        ⌜decodeItemInputBytes args !! index = Some vmem⌝ -∗
        ⌜eq_rect 8%N bv n2 8%N Heq = vmem⌝ -∗
        decodeItemInputPointer args ↦ₘ∗ decodeItemInputBytes args -∗ result)%I))).
  iExact "Hsource".
Qed.

Require Import ZesuSsz.Automation.Switches.PureFactExistential.

Lemma pure_fact_existential_dependent_load `{!islaG Sigma}
    args n i payloadStart lengthBytes (n2 : bv 8) (result : iProp Sigma) :
  decodeItemByteFoldFacts args n i payloadStart lengthBytes ->
  @ZesuPureFactIntro Sigma
    (∃ index : nat, ⌜Z.of_nat index =
      (payloadStart + i + 0 - decodeItemInputPointer args) `div` 1⌝ ∗
      ⌜(index < length (decodeItemInputBytes args))%nat⌝ ∗
      ∃ Heq : 8%N = 8%N, ∀ vmem : bv 8,
        ⌜decodeItemInputBytes args !! index = Some vmem⌝ -∗
        ⌜eq_rect 8%N bv n2 8%N Heq = vmem⌝ -∗
        decodeItemInputPointer args ↦ₘ∗ decodeItemInputBytes args -∗ result)%I
    (⌜decodeItemByteFoldFacts args n i payloadStart lengthBytes⌝ ∗
      ⌜(Z.to_nat (1 + i)%Z < length (decodeItemInputBytes args))%nat⌝ ∗
      ∃ Heq : 8%N = 8%N, ∀ vmem : bv 8,
        ⌜decodeItemInputBytes args !! Z.to_nat (1 + i)%Z = Some vmem⌝ -∗
        ⌜eq_rect 8%N bv n2 8%N Heq = vmem⌝ -∗
        decodeItemInputPointer args ↦ₘ∗ decodeItemInputBytes args -∗ result)%I.
Proof.
  intros Hfold. unfold ZesuPureFactIntro. iIntros "Hsource". pure_fact_existential_bind_environment.
  zesu_pure_fact_hints_if_enabled. iExact "Hsource".
Qed.

Lemma pure_fact_existential_unregistered {Sigma} (chosen : nat) (resource : iProp Sigma) :
  resource ⊢ ∃ witness : nat, ⌜witness = chosen⌝ ∗ resource.
Proof.
  iIntros "Hresource". pure_fact_existential_bind_environment. Fail zesu_pure_fact_existential_if_enabled.
  iExists chosen. iFrame. done.
Qed.

Ltac2 rec pure_intro_let_count (term : constr) :=
  let children terms := Array.fold_left
    (fun count child => Int.add count (pure_intro_let_count child)) 0 terms in
  let binders terms := Array.fold_left
    (fun count binder => Int.add count (pure_intro_let_count (Constr.Binder.type binder))) 0 terms in
  match Constr.Unsafe.kind term with
  | Constr.Unsafe.App head args => Int.add (pure_intro_let_count head) (children args)
  | Constr.Unsafe.Evar _ args => children args
  | Constr.Unsafe.Cast value _ ty => Int.add (pure_intro_let_count value) (pure_intro_let_count ty)
  | Constr.Unsafe.Prod binder body => Int.add (pure_intro_let_count (Constr.Binder.type binder)) (pure_intro_let_count body)
  | Constr.Unsafe.Lambda binder body => Int.add (pure_intro_let_count (Constr.Binder.type binder)) (pure_intro_let_count body)
  | Constr.Unsafe.LetIn binder value body => Int.add 1
      (Int.add (pure_intro_let_count (Constr.Binder.type binder))
        (Int.add (pure_intro_let_count value) (pure_intro_let_count body)))
  | Constr.Unsafe.Proj _ _ value => pure_intro_let_count value
  | Constr.Unsafe.Case _ predicate inv value branches =>
      let (ty, _) := predicate in
      let count := match inv with
        | Constr.Unsafe.NoInvert => 0
        | Constr.Unsafe.CaseInvert args => children args end in
      Int.add count (Int.add (pure_intro_let_count ty)
        (Int.add (pure_intro_let_count value) (children branches)))
  | Constr.Unsafe.Fix _ _ bs terms => Int.add (binders bs) (children terms)
  | Constr.Unsafe.CoFix _ bs terms => Int.add (binders bs) (children terms)
  | Constr.Unsafe.Array _ args value ty => Int.add (children args)
      (Int.add (pure_intro_let_count value) (pure_intro_let_count ty))
  | _ => 0
  end.

Ltac pure_fact_existential_check_cleanup :=
  match goal with
  | alias := ?body |- _ =>
      lazymatch body with
      | (fun _ => _) => fail 1 "The continuation alias remains."
      | _ => fail 0
      end
  | _ => idtac
  end;
  ltac2:(Control.enter (fun () =>
    Control.assert_true (Int.equal (pure_intro_let_count (Control.goal ())) 0))).

Ltac pure_fact_existential_check_exact expected :=
  let actual := lazymatch goal with |- ?goal => constr:(goal) end in
  constr_eq actual expected;
  pure_fact_existential_check_cleanup.

Lemma pure_fact_existential_shelved_continuation `{!islaG Sigma}
    args n i payloadStart lengthBytes (n2 : bv 8) (result : iProp Sigma) :
  decodeItemByteFoldFacts args n i payloadStart lengthBytes ->
  @ZesuPureFactIntro Sigma
    (∃ index : nat, ⌜Z.of_nat index =
      (payloadStart + i + 0 - decodeItemInputPointer args) `div` 1⌝ ∗
      ⌜(index < length (decodeItemInputBytes args))%nat⌝ ∗
      ∃ Heq : 8%N = 8%N, ∀ vmem : bv 8,
        ⌜decodeItemInputBytes args !! index = Some vmem⌝ -∗
        ⌜eq_rect 8%N bv n2 8%N Heq = vmem⌝ -∗
        decodeItemInputPointer args ↦ₘ∗ decodeItemInputBytes args -∗ result)%I
    (⌜decodeItemByteFoldFacts args n i payloadStart lengthBytes⌝ ∗
      ⌜(Z.to_nat (1 + i)%Z < length (decodeItemInputBytes args))%nat⌝ ∗
      ∃ Heq : 8%N = 8%N, ∀ vmem : bv 8,
        ⌜decodeItemInputBytes args !! Z.to_nat (1 + i)%Z = Some vmem⌝ -∗
        ⌜eq_rect 8%N bv n2 8%N Heq = vmem⌝ -∗
        decodeItemInputPointer args ↦ₘ∗ decodeItemInputBytes args -∗ result)%I.
Proof.
  intros Hfold.
  let source := lazymatch goal with |- ZesuPureFactIntro _ ?source => constr:(source) end in
  unfold ZesuPureFactIntro; iIntros "Hsource"; pure_fact_existential_bind_environment;
  let expected := lazymatch goal with
    | |- envs_entails ?environment _ =>
      let concrete := eval hnf in environment in
      lazymatch concrete with Envs ?persistent ?spatial ?counter =>
      let next := eval compute in (Pos.succ counter) in
      constr:(envs_entails (Envs persistent spatial next) source) end end in
  unshelve (zesu_pure_fact_hints_if_enabled;
    pure_fact_existential_check_exact expected; shelve);
  pure_fact_existential_check_exact expected;
  iExact "Hsource".
Qed.

Lemma pure_fact_existential_shared_evar_rollback {Sigma}
    (chosen : nat) (resource : nat -> iProp Sigma) : True.
Proof.
  let hole := open_constr:(_ : nat) in
  let shared := eval cbv beta iota zeta in hole in
  assert (Hprobe : resource shared ⊢
    ∃ witness : nat, ⌜witness = shared⌝ ∗ resource shared);
  [ iIntros "Hresource"; pure_fact_existential_bind_environment;
    let before := lazymatch goal with |- ?goal => constr:(goal) end in
    first [ zesu_pure_fact_existential_if_enabled;
      fail 1 "The lookup succeeded." | idtac ];
    is_evar shared;
    pure_fact_existential_check_exact before;
    unify shared chosen;
    pure_fact_existential_check_exact before;
    iExists chosen; iFrame; done
  | exact I ].
Qed.

Lemma pure_fact_existential_shared_evar_success `{!islaG Sigma}
    args n i payloadStart lengthBytes (n2 : bv 8) (result : iProp Sigma) :
  decodeItemByteFoldFacts args n i payloadStart lengthBytes ->
  True.
Proof.
  intros Hfold.
  let hole := open_constr:(_ : bv 8) in
  let shared := eval cbv beta iota zeta in hole in
  assert (Hprobe : @ZesuPureFactIntro Sigma
    (∃ index : nat, ⌜Z.of_nat index =
      (payloadStart + i + 0 - decodeItemInputPointer args) `div` 1⌝ ∗
      ⌜(index < length (decodeItemInputBytes args))%nat⌝ ∗
      ∃ Heq : 8%N = 8%N, ∀ vmem : bv 8,
        ⌜decodeItemInputBytes args !! index = Some vmem⌝ -∗
        ⌜eq_rect 8%N bv shared 8%N Heq = vmem⌝ -∗
        decodeItemInputPointer args ↦ₘ∗ decodeItemInputBytes args -∗ result)%I
    (⌜decodeItemByteFoldFacts args n i payloadStart lengthBytes⌝ ∗
      ⌜(Z.to_nat (1 + i)%Z < length (decodeItemInputBytes args))%nat⌝ ∗
      ∃ Heq : 8%N = 8%N, ∀ vmem : bv 8,
        ⌜decodeItemInputBytes args !! Z.to_nat (1 + i)%Z = Some vmem⌝ -∗
        ⌜eq_rect 8%N bv shared 8%N Heq = vmem⌝ -∗
        decodeItemInputPointer args ↦ₘ∗ decodeItemInputBytes args -∗ result)%I);
  [ let source := lazymatch goal with |- ZesuPureFactIntro _ ?source => constr:(source) end in
    unfold ZesuPureFactIntro; iIntros "Hsource"; pure_fact_existential_bind_environment;
    let expected := lazymatch goal with
      | |- envs_entails ?environment _ =>
        let concrete := eval hnf in environment in
        lazymatch concrete with Envs ?persistent ?spatial ?counter =>
        let next := eval compute in (Pos.succ counter) in
        constr:(envs_entails (Envs persistent spatial next) source) end end in
    unshelve (zesu_pure_fact_hints_if_enabled;
      is_evar shared; pure_fact_existential_check_exact expected; shelve);
    is_evar shared; pure_fact_existential_check_exact expected;
    unify shared n2;
    constr_eq shared n2;
    pure_fact_existential_check_exact expected;
    iExact "Hsource"
  | exact I ].
Qed.

Lemma pure_fact_existential_nonmatching {Sigma} (resource : iProp Sigma) :
  resource ⊢ ∃ witness : nat, resource.
Proof.
  iIntros "Hresource". pure_fact_existential_bind_environment. Fail zesu_pure_fact_existential_if_enabled.
  unfold IPM_TEST_ALIAS. iExists 0%nat. iExact "Hresource".
Qed.

Lemma pure_fact_existential_cleanup_detects_let (chosen : nat) : True.
Proof.
  assert (Hlet : let leaked := chosen in leaked = chosen).
  { Fail pure_fact_existential_check_cleanup. reflexivity. }
  exact I.
Qed.

Print Assumptions pure_fact_existential_shelved_continuation.
Print Assumptions pure_fact_existential_shared_evar_rollback.
Print Assumptions pure_fact_existential_off.
Print Assumptions pure_fact_existential_dependent_load.
Print Assumptions pure_fact_existential_unregistered.
Print Assumptions pure_fact_existential_shared_evar_success.
Print Assumptions pure_fact_existential_nonmatching.
Print Assumptions pure_fact_existential_cleanup_detects_let.
