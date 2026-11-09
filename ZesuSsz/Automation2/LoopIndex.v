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

(* A cursor register stepped by one, on either edge of the exit branch,
   advances the loop index that its retained cursor conjunct names. *)
Ltac zesu_loop_cursor_conjunct cursor index statement :=
  lazymatch statement with
  | ?left /\ ?right =>
      first [zesu_loop_cursor_conjunct cursor index left |
             zesu_loop_cursor_conjunct cursor index right]
  | bv_unsigned cursor = ?target => lazymatch target with context [index] => idtac end
  end.

Ltac zesu_loop_cursor_step cursor one limit continuation :=
  is_var cursor;
  assert_fails (has_evar limit);
  let unit := eval vm_compute in (bv_unsigned one) in
  constr_eq unit 1%Z;
  match goal with
  | index : lvar "zesuLoopIndex" Z |- _ =>
      match goal with
      | Hcursor : ?statement |- _ =>
          lazymatch type of statement with Prop => idtac end;
          zesu_loop_cursor_conjunct cursor index statement
      end;
      continuation index
  end.

Ltac zesu_loop_cursor_guard continuation :=
  match goal with
  | Hbranch : @bv_add ?width ?cursor ?one <> ?limit |- _ =>
      zesu_loop_cursor_step cursor one limit continuation
  | Hbranch : @bv_add ?width ?cursor ?one = ?limit |- _ =>
      zesu_loop_cursor_step cursor one limit continuation
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
  first [
    zesu_loop_guard ltac:(fun index count =>
      notypeclasses refine (simpl_exist_lvar _ Z (index + 1)%Z "zesuLoopIndex" _);
      constructor; by unlock)
  | zesu_loop_cursor_guard ltac:(fun index =>
      notypeclasses refine (simpl_exist_lvar _ Z (index + 1)%Z "zesuLoopIndex" _);
      constructor; by unlock)
    (* Without a cursor step, a successor of the exit keeps the index. *)
  | match goal with
    | index : lvar "zesuLoopIndex" Z |- _ =>
        notypeclasses refine (simpl_exist_lvar _ Z index "zesuLoopIndex" _);
        constructor; by unlock
    end].

#[export] Hint Extern 1 (SimplExist (lvar "zesuLoopCount" Z) _) =>
  zesu_simpl_exist_loop_count : typeclass_instances.
#[export] Hint Extern 1 (SimplExist (lvar "zesuLoopIndex" Z) _) =>
  zesu_simpl_exist_loop_index : typeclass_instances.
