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
    | Hbranch : ?branch_lhs <> ?branch_rhs |- _ =>
      lazymatch branch_lhs with
      | @bv_add 64 (Z_to_bv 64 (Z.add ?ps ?j)) ?one =>
        constr_eq j i;
        let unit_word := constr:((1%bv : bv 64)) in
        constr_eq one unit_word;
        assert_fails (has_evar ps);
        let expected_right := constr:(Z_to_bv 64 (Z.add ps n)) in
        assert_fails (has_evar branch_rhs);
        assert_fails (has_evar expected_right);
        unify branch_rhs expected_right;
        continuation i n
      end
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
