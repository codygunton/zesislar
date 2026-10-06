Require Import ZesuSsz.Automation.All.
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Automation.Switches.EvarSideconditionGuard.

Lemma evar_sidecondition_shelved : True.
Proof.
  evar (index : nat).
  assert (Hindex : SHELVED_SIDECOND (index < 2)%nat).
  { let before := lazymatch goal with |- ?G => constr:(G) end in
    zesu_defer_unresolved_sidecondition_if_enabled;
    zesu_finish;
    let after := lazymatch goal with |- ?G => constr:(G) end in
    constr_eq before after.
    let value := eval unfold index in index in is_evar value.
    instantiate (index := 0%nat).
    zesu_finish. }
  exact I.
Qed.

Lemma evar_sidecondition_pure : True.
Proof.
  evar (index : nat).
  assert (Hindex : (index < 2)%nat).
  { let before := lazymatch goal with |- ?G => constr:(G) end in
    zesu_defer_unresolved_sidecondition_if_enabled;
    zesu_finish;
    let after := lazymatch goal with |- ?G => constr:(G) end in
    constr_eq before after.
    let value := eval unfold index in index in is_evar value.
    instantiate (index := 0%nat).
    zesu_finish. }
  exact I.
Qed.

Lemma evar_sidecondition_closed : SHELVED_SIDECOND (1 < 2)%nat.
Proof.
  Fail zesu_defer_unresolved_sidecondition_if_enabled.
  zesu_finish.
Qed.

Lemma evar_sidecondition_iris `{!islaG Sigma} : True.
Proof.
  evar (index : nat).
  assert (Hiris : ((⌜index = 0%nat⌝ : iProp Sigma) ⊢ ⌜index = 0%nat⌝)%I).
  { Fail zesu_defer_unresolved_sidecondition_if_enabled.
    reflexivity. }
  instantiate (index := 0%nat).
  exact I.
Qed.

Lemma evar_sidecondition_alias_chain : True.
Proof.
  evar (index : nat).
  pose (alias := index).
  assert (Hindex : SHELVED_SIDECOND (alias < 2)%nat).
  { zesu_defer_unresolved_sidecondition_if_enabled.
    zesu_finish.
    let value := eval unfold index in index in is_evar value.
    instantiate (index := 0%nat).
    zesu_finish. }
  exact I.
Qed.

Lemma evar_sidecondition_symbolic (index : nat) : (index < 2)%nat -> True.
Proof.
  intro Hbound.
  assert (Hindex : (index < 2)%nat).
  { Fail zesu_defer_unresolved_sidecondition_if_enabled.
    exact Hbound. }
  exact I.
Qed.
