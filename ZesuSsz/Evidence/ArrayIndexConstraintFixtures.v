Require Import ZesuSsz.Automation.All.
From Coq Require Import ZArith List.
From Ltac2 Require Import Ltac2 List Int.
Open Scope Z_scope.
Set Default Proof Mode "Classic".

Ltac2 @ external fixture_array_constraints :
  constr -> constr -> constr -> constr -> evar list :=
  "zesu-signature-gates.plugin" "array_index_constraints".

Ltac fixture_selected pointer index :=
  let query := ltac2:(pointer index |-
    let keys := fixture_array_constraints
      (Option.get (Ltac1.to_constr pointer))
      (Option.get (Ltac1.to_constr index))
      constr:(lithium.proof_state.SHELVED_SIDECOND) constr:(@eq) in
    if Int.equal (List.length keys) 1 then ()
    else Control.zero (Tactic_failure None)) in
  query pointer index.

Ltac fixture_unselected pointer index :=
  let query := ltac2:(pointer index |-
    let keys := fixture_array_constraints
      (Option.get (Ltac1.to_constr pointer))
      (Option.get (Ltac1.to_constr index))
      constr:(lithium.proof_state.SHELVED_SIDECOND) constr:(@eq) in
    if Int.equal (List.length keys) 0 then ()
    else Control.zero (Tactic_failure None)) in
  query pointer index.

(* These synthetic controls test selection only. The final proof assigns a
   fixture value after the selection assertion. No native witness is chosen. *)

Lemma constraint_direct (pointer : Z) : True.
Proof.
  evar (nativeIndex : nat).
  assert (candidate : lithium.proof_state.SHELVED_SIDECOND (Z.of_nat nativeIndex = pointer + 8 - pointer)) by shelve.
  fixture_selected pointer nativeIndex.
  exact I.
  Unshelve.
  all: try exact 8%nat.
  all: unfold lithium.proof_state.SHELVED_SIDECOND; cbn; lia.
Qed.

Lemma constraint_alias (pointer : Z) : True.
Proof.
  evar (nativeIndex : nat).
  pose (alias := nativeIndex).
  assert (candidate : lithium.proof_state.SHELVED_SIDECOND (Z.of_nat alias = pointer + 8 - pointer)) by shelve.
  fixture_selected pointer nativeIndex.
  exact I.
  Unshelve.
  all: try exact 8%nat.
  all: unfold lithium.proof_state.SHELVED_SIDECOND; cbn; lia.
Qed.

Lemma constraint_alias_chain (pointer : Z) : True.
Proof.
  evar (nativeIndex : nat).
  pose (alias := nativeIndex).
  pose (alias2 := alias).
  assert (candidate : lithium.proof_state.SHELVED_SIDECOND (Z.of_nat alias2 = pointer + 8 - pointer)) by shelve.
  fixture_selected pointer nativeIndex.
  exact I.
  Unshelve.
  all: try exact 8%nat.
  all: unfold lithium.proof_state.SHELVED_SIDECOND; cbn; lia.
Qed.

Lemma constraint_binder_alias (pointer : Z) : True.
Proof.
  evar (nativeIndex : nat).
  pose (alias := nativeIndex).
  assert (candidate : lithium.proof_state.SHELVED_SIDECOND ((let binderAlias := alias in Z.of_nat binderAlias) = pointer + 8 - pointer)) by shelve.
  fixture_selected pointer nativeIndex.
  exact I.
  Unshelve.
  all: try exact 8%nat.
  all: unfold lithium.proof_state.SHELVED_SIDECOND; cbn; lia.
Qed.

Lemma constraint_lambda (pointer : Z) : True.
Proof.
  evar (nativeIndex : nat).
  pose (alias := nativeIndex).
  assert (candidate : lithium.proof_state.SHELVED_SIDECOND ((fun ignored : nat => Z.of_nat alias) 0%nat = pointer + 8 - pointer)) by shelve.
  fixture_selected pointer nativeIndex.
  exact I.
  Unshelve.
  all: try exact 8%nat.
  all: unfold lithium.proof_state.SHELVED_SIDECOND; cbn; lia.
Qed.

Lemma constraint_closed (pointer : Z) : True.
Proof.
  evar (nativeIndex : nat).
  assert (candidate : lithium.proof_state.SHELVED_SIDECOND (pointer = pointer)) by shelve.
  fixture_unselected pointer nativeIndex.
  exact I.
  Unshelve.
  all: try exact 8%nat.
  all: unfold lithium.proof_state.SHELVED_SIDECOND; cbn; lia.
Qed.

Lemma constraint_wrong_pointer (pointer : Z) : True.
Proof.
  evar (nativeIndex : nat).
  assert (candidate : lithium.proof_state.SHELVED_SIDECOND (Z.of_nat nativeIndex = 8)) by shelve.
  fixture_unselected 41%Z nativeIndex.
  exact I.
  Unshelve.
  all: try exact 8%nat.
  all: unfold lithium.proof_state.SHELVED_SIDECOND; cbn; lia.
Qed.

Lemma constraint_alias_bound (pointer : Z) : True.
Proof.
  evar (nativeIndex : nat).
  pose (alias1 := nativeIndex).
  pose (alias2 := alias1).
  pose (alias3 := alias2).
  pose (alias4 := alias3).
  pose (alias5 := alias4).
  pose (alias6 := alias5).
  pose (alias7 := alias6).
  pose (alias8 := alias7).
  pose (alias9 := alias8).
  pose (alias10 := alias9).
  pose (alias11 := alias10).
  pose (alias12 := alias11).
  pose (alias13 := alias12).
  pose (alias14 := alias13).
  pose (alias15 := alias14).
  pose (alias16 := alias15).
  pose (alias17 := alias16).
  pose (alias18 := alias17).
  pose (alias19 := alias18).
  pose (alias20 := alias19).
  pose (alias21 := alias20).
  pose (alias22 := alias21).
  pose (alias23 := alias22).
  pose (alias24 := alias23).
  pose (alias25 := alias24).
  pose (alias26 := alias25).
  pose (alias27 := alias26).
  pose (alias28 := alias27).
  pose (alias29 := alias28).
  pose (alias30 := alias29).
  pose (alias31 := alias30).
  pose (alias32 := alias31).
  pose (alias33 := alias32).
  pose (alias34 := alias33).
  assert (candidate : lithium.proof_state.SHELVED_SIDECOND (Z.of_nat alias34 = pointer + 8 - pointer)) by shelve.
  fixture_selected pointer nativeIndex.
  exact I.
  Unshelve.
  all: try exact 8%nat.
  all: unfold lithium.proof_state.SHELVED_SIDECOND; cbn; lia.
Qed.

Lemma constraint_node_bound (pointer : Z) : True.
Proof.
  evar (nativeIndex : nat).
  assert (candidate : lithium.proof_state.SHELVED_SIDECOND (Z.of_nat (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (nativeIndex))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) = pointer + 528 - pointer)) by shelve.
  fixture_selected pointer nativeIndex.
  exact I.
  Unshelve.
  all: try exact 8%nat.
  all: unfold lithium.proof_state.SHELVED_SIDECOND; cbn; lia.
Qed.
