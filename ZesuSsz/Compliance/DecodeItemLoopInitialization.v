From Coq Require Import ZArith.
From lithium Require Import lvar simpl_classes.
Require Import isla.automation.
Require Import ZesuSsz.Automation.LoopIndex.
Require Import ZesuSsz.Contracts.RlpDecodeItemByteFold.

(* Initial entry has no taken back edge. Its existing fold fact fixes both binders. *)
Ltac decodeItem_loop_initial_witness continuation :=
  unLET;
  lazymatch goal with
  | Hguard : (?i < ?n)%Z,
    Hbranch : (Z_to_bv 64 (?ps + ?i)%Z + 1)%bv <>
      Z_to_bv 64 (?ps + ?n)%Z |- _ => fail 1 "taken back edge"
  | _ => idtac
  end;
  let first_fact := match goal with
  | Hinitial : decodeItemByteFoldFacts ?args ?n 0 ?ps ?bytes |- _ => constr:(Hinitial)
  end in
  let last_fact := match reverse goal with
  | Hinitial : decodeItemByteFoldFacts ?args ?n 0 ?ps ?bytes |- _ => constr:(Hinitial)
  end in
  constr_eq first_fact last_fact;
  let fact_type := type of first_fact in
  assert_fails (has_evar fact_type);
  lazymatch fact_type with
  | decodeItemByteFoldFacts ?args ?n 0 ?ps ?bytes => continuation n
  end.

Ltac decodeItem_simpl_exist_initial_count :=
  lazymatch goal with |- @SimplExist _ ?T _ =>
    constr_eq T (lvar "zesuLoopCount" Z)
  end;
  decodeItem_loop_initial_witness ltac:(fun count =>
    notypeclasses refine (simpl_exist_lvar _ Z count "zesuLoopCount" _);
    constructor; by unlock).

Ltac decodeItem_simpl_exist_initial_index :=
  lazymatch goal with |- @SimplExist _ ?T _ =>
    constr_eq T (lvar "zesuLoopIndex" Z)
  end;
  decodeItem_loop_initial_witness ltac:(fun count =>
    notypeclasses refine (simpl_exist_lvar _ Z 0%Z "zesuLoopIndex" _);
    constructor; by unlock).

#[export] Hint Extern 3 (SimplExist (lvar "zesuLoopCount" Z) _) =>
  decodeItem_simpl_exist_initial_count : typeclass_instances.
#[export] Hint Extern 3 (SimplExist (lvar "zesuLoopIndex" Z) _) =>
  decodeItem_simpl_exist_initial_index : typeclass_instances.
