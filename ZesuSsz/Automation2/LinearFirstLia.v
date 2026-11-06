From Coq Require Import ZArith.ZArith micromega.Lia micromega.Zify omega.PreOmega.
From Ltac2 Require Ltac2.
Set Default Proof Mode "Classic".
Local Open Scope Z_scope.

Ltac zesu_zify_prefix :=
  intros; Zify.zify_pre_hook; Zify.zify_elim_let; Zify.zify_op; (Zify.zify_iter_specs);
  Zify.zify_to_euclidean_division_equations.

Ltac zesu_lia_has_divmod :=
  match goal with
  | |- context [Z.div _ _] => idtac
  | |- context [Z.modulo _ _] => idtac
  | |- context [Z.quot _ _] => idtac
  | |- context [Z.rem _ _] => idtac
  | _ : context [Z.div _ _] |- _ => idtac
  | _ : context [Z.modulo _ _] |- _ => idtac
  | _ : context [Z.quot _ _] |- _ => idtac
  | _ : context [Z.rem _ _] |- _ => idtac
  end.

Inductive zesu_divmod_done (x y : Z) : Prop := zesu_divmod_done_intro.

Ltac zesu_zlit t :=
  lazymatch t with
  | Z0 => idtac | Zpos _ => idtac | Zneg _ => idtac
  | Z.pow ?a ?b => zesu_zlit a; zesu_zlit b
  | Z.add ?a ?b => zesu_zlit a; zesu_zlit b
  | Z.sub ?a ?b => zesu_zlit a; zesu_zlit b
  | Z.mul ?a ?b => zesu_zlit a; zesu_zlit b
  | Z.opp ?a => zesu_zlit a
  | Z.of_N ?n => lazymatch n with N0 => idtac | Npos _ => idtac end
  | Z.of_nat ?n => zesu_nlit n
  end
with zesu_nlit t :=
  lazymatch t with
  | O => idtac | S ?n => zesu_nlit n
  end.

Ltac zesu_poslit y :=
  zesu_zlit y; assert_succeeds (assert (0 < y) by exact (proj1 (Z.ltb_lt 0 y) eq_refl)).

Ltac zesu_divmod_all_literal :=
  assert_fails (idtac; match goal with
  | |- context [Z.div _ ?y] => assert_fails (idtac; zesu_poslit y)
  | |- context [Z.modulo _ ?y] => assert_fails (idtac; zesu_poslit y)
  | _ : context [Z.div _ ?y] |- _ => assert_fails (idtac; zesu_poslit y)
  | _ : context [Z.modulo _ ?y] |- _ => assert_fails (idtac; zesu_poslit y)
  | |- context [Z.quot _ _] => idtac
  | |- context [Z.rem _ _] => idtac
  | _ : context [Z.quot _ _] |- _ => idtac
  | _ : context [Z.rem _ _] |- _ => idtac
  end).

Ltac zesu_divmod_fact x y :=
  lazymatch goal with
  | _ : zesu_divmod_done x y |- _ => fail
  | _ =>
    let Hpos := fresh "Hpos" in
    assert (Hpos : 0 < y) by exact (proj1 (Z.ltb_lt 0 y) eq_refl);
    pose proof (Z.div_mod x y (Z.neq_sym _ _ (Z.lt_neq _ _ Hpos)));
    pose proof (Z.mod_pos_bound x y Hpos);
    clear Hpos;
    pose proof (zesu_divmod_done_intro x y)
  end.

Ltac zesu_divmod_literal_facts :=
  repeat match goal with
  | |- context [Z.div ?x ?y] => zesu_divmod_fact x y
  | |- context [Z.modulo ?x ?y] => zesu_divmod_fact x y
  | _ : context [Z.div ?x ?y] |- _ => zesu_divmod_fact x y
  | _ : context [Z.modulo ?x ?y] |- _ => zesu_divmod_fact x y
  end.

Inductive zesu_divmod_seen (t : Z) : Prop := zesu_divmod_seen_intro.

Ltac zesu_divmod_mark t :=
  lazymatch goal with
  | _ : zesu_divmod_seen t |- _ => fail
  | _ => pose proof (zesu_divmod_seen_intro t)
  end.

Ltac zesu_divmod_mark_all :=
  repeat match goal with
  | |- context [Z.div ?x ?y] => zesu_divmod_mark (Z.div x y)
  | |- context [Z.modulo ?x ?y] => zesu_divmod_mark (Z.modulo x y)
  | |- context [Z.quot ?x ?y] => zesu_divmod_mark (Z.quot x y)
  | |- context [Z.rem ?x ?y] => zesu_divmod_mark (Z.rem x y)
  | _ : context [Z.div ?x ?y] |- _ => zesu_divmod_mark (Z.div x y)
  | _ : context [Z.modulo ?x ?y] |- _ => zesu_divmod_mark (Z.modulo x y)
  | _ : context [Z.quot ?x ?y] |- _ => zesu_divmod_mark (Z.quot x y)
  | _ : context [Z.rem ?x ?y] |- _ => zesu_divmod_mark (Z.rem x y)
  end.

Ltac2 zesu_divmod_count () : Ltac2.Init.int :=
  Ltac2.List.length (Ltac2.List.filter (fun h =>
    let (_, _, ty) := h in
    match Ltac2.Constr.Unsafe.kind ty with
    | Ltac2.Constr.Unsafe.App f _ => Ltac2.Constr.equal f constr:(zesu_divmod_seen)
    | _ => Ltac2.Init.false
    end) (Ltac2.Control.hyps ())).

Ltac2 zesu_divmod_bound () : Ltac2.Init.int := 24.

Ltac2 zesu_divmod_within_bound () :=
  if Ltac2.Int.gt (zesu_divmod_count ()) (zesu_divmod_bound ())
  then Ltac2.Control.zero (Ltac2.Init.Tactic_failure Ltac2.Init.None) else ().

Ltac zesu_divmod_guard :=
  assert_succeeds (zesu_divmod_mark_all; ltac2:(zesu_divmod_within_bound ())).

Ltac zesu_lia_divmod_step :=
  first [ zesu_divmod_all_literal; zesu_divmod_literal_facts
        | zesu_divmod_guard; Zify.zify_post_hook ].

Ltac zesu_lia_linear_first3 :=
  zesu_zify_prefix;
  first [ solve [Zify.zify_saturate; xlia Lia.zchecker]
        | zesu_lia_has_divmod;
          zesu_lia_divmod_step; Zify.zify_saturate; xlia Lia.zchecker ].
