Require Import ZesuSsz.Automation.All.
Require Import isla.riscv64.riscv64.
From lithium Require Import lvar simpl_classes.
Open Scope Z_scope.

Set Default Proof Using "Type".

Section tests.
Context {Sigma : gFunctors}.

Lemma loop_index_unique (i n ps : Z) :
  i < n -> (Z_to_bv 64 (ps+i) + 1)%bv <> Z_to_bv 64 (ps+n) ->
  @SimplExist Sigma (lvar "zesuLoopIndex" Z) (fun P => P (i+1)).
Proof. intros Hguard Hbranch. typeclasses eauto. Qed.

Lemma loop_count_unique (i n ps : Z) :
  i < n -> (Z_to_bv 64 (ps+i) + 1)%bv <> Z_to_bv 64 (ps+n) ->
  @SimplExist Sigma (lvar "zesuLoopCount" Z) (fun P => P n).
Proof. intros Hguard Hbranch. typeclasses eauto. Qed.

Lemma loop_index_alias (i n ps : Z) :
  i < n -> let next := (Z_to_bv 64 (ps+i) + 1)%bv in
  next <> Z_to_bv 64 (ps+n) ->
  @SimplExist Sigma (lvar "zesuLoopIndex" Z) (fun P => P (i+1)).
Proof. intros Hguard next Hbranch. typeclasses eauto. Qed.

Lemma loop_two_guards_refuse (i n ps : Z) :
  i < n -> i < n ->
  (Z_to_bv 64 (ps+i) + 1)%bv <> Z_to_bv 64 (ps+n) -> True.
Proof.
  intros Hguard Hother Hbranch.
  Fail zesu_loop_guard ltac:(fun index count => idtac).
  exact I.
Qed.

Lemma loop_missing_branch_refuses (i n : Z) : i < n -> True.
Proof.
  intro Hguard.
  Fail zesu_loop_guard ltac:(fun index count => idtac).
  exact I.
Qed.
Lemma loop_branch_rhs_alias (i n ps : Z) :
  i<n -> let endpoint := Z_to_bv 64 (ps+n) in
  (Z_to_bv 64 (ps+i)+1)%bv <> endpoint ->
  @SimplExist Sigma (lvar "zesuLoopIndex" Z) (fun P => P (i+1)).
Proof. intros Hguard endpoint Hbranch. zesu_simpl_exist_loop_index. Qed.

End tests.
