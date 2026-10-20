From Coq Require Import ZArith.
From lithium Require Import lvar simpl_classes.
Require Import isla.automation.

(* Only a unique guard paired with the taken back edge selects a witness. *)
Ltac zesu_loop_guard continuation :=
  let first_guard := match goal with
  | Hguard : (?i < ?n)%Z,
    Hbranch : (Z_to_bv 64 (?ps + ?i)%Z + 1)%bv <>
      Z_to_bv 64 (?ps + ?n)%Z |- _ => constr:(Hguard)
  end in
  let last_guard := match reverse goal with
  | Hguard : (?i < ?n)%Z,
    Hbranch : (Z_to_bv 64 (?ps + ?i)%Z + 1)%bv <>
      Z_to_bv 64 (?ps + ?n)%Z |- _ => constr:(Hguard)
  end in
  constr_eq first_guard last_guard;
  let guard_type := type of first_guard in
  lazymatch guard_type with (?i < ?n)%Z =>
    assert_fails (has_evar i); assert_fails (has_evar n);
    match goal with
    | Hbranch : (Z_to_bv 64 (?ps + i)%Z + 1)%bv <>
        Z_to_bv 64 (?ps + n)%Z |- _ =>
      assert_fails (has_evar ps); continuation i n
    end
  end.

Ltac zesu_simpl_exist_loop_count :=
  lazymatch goal with |- @SimplExist _ ?T _ =>
    constr_eq T (lvar "zesuLoopCount" Z)
  end;
  unLET;
  zesu_loop_guard ltac:(fun index count =>
    notypeclasses refine (simpl_exist_lvar _ Z count "zesuLoopCount" _);
    constructor; by unlock).

Ltac zesu_simpl_exist_loop_index :=
  lazymatch goal with |- @SimplExist _ ?T _ =>
    constr_eq T (lvar "zesuLoopIndex" Z)
  end;
  unLET;
  zesu_loop_guard ltac:(fun index count =>
    notypeclasses refine (simpl_exist_lvar _ Z (index + 1)%Z "zesuLoopIndex" _);
    constructor; by unlock).

#[export] Hint Extern 1 (SimplExist (lvar "zesuLoopCount" Z) _) =>
  zesu_simpl_exist_loop_count : typeclass_instances.
#[export] Hint Extern 1 (SimplExist (lvar "zesuLoopIndex" Z) _) =>
  zesu_simpl_exist_loop_index : typeclass_instances.
