Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Automation.PureFacts.
Local Open Scope Z_scope.

(* Wrapped-word helpers. The versioned proof profile controls their activation. *)
Ltac zesu_wrapped_word_range arithmetic :=
  try (apply andb_true_iff; split);
  try apply bool_decide_eq_true_2;
  rewrite !bv_add_unsigned !Z_to_bv_unsigned ;
  repeat rewrite bv_unsigned_BV;
  repeat rewrite bv_wrap_add_idemp_l;
  repeat (rewrite <- Z.add_assoc; rewrite bv_wrap_add_idemp_l);
  lazymatch goal with
  | |- context [bv_wrap ?width (?base + ?offset)] =>
    let adjusted := constr:(offset - bv_modulus width) in
    let Hrange := fresh "HwrappedRange" in
    assert (Hrange : 0 <= base + adjusted < bv_modulus width) by arithmetic;
    let Hword := fresh "HwrappedWord" in
    assert (Hword : bv_wrap width (base + offset) = base + adjusted) by
      (replace (base + offset) with (base + adjusted + bv_modulus width) by ring;
       rewrite bv_wrap_add_modulus_1; apply bv_wrap_small; exact Hrange);
    rewrite Hword
  end;
  cbv [bv_unsigned Z_to_bv bv_wrap bv_modulus];
  arithmetic.

Ltac zesu_reduce_closed_Z_aliases :=
  repeat match goal with
  | Hconstant : context [?scalar] |- _ =>
    let scalar_type := type of scalar in
    constr_eq scalar_type Z;
    is_closed_term scalar;
    let head := get_head scalar in
    constr_eq head scalar;
    assert_fails (is_var scalar);
    let reduced := eval cbv delta [scalar] in scalar in
    progress change scalar with reduced in Hconstant
  end.


Lemma zesu_wrapped_add_unsigned_small (width : N) (base : Z) (left right : bv width) :
  0 <= base + (bv_unsigned left + bv_unsigned right - bv_modulus width) < bv_modulus width ->
  bv_unsigned (Z_to_bv width base + left + right) =
    base + (bv_unsigned left + bv_unsigned right - bv_modulus width).
Proof.
  intros Hrange.
  rewrite !bv_add_unsigned Z_to_bv_unsigned.
  rewrite bv_wrap_add_idemp_l.
  rewrite <- Z.add_assoc, bv_wrap_add_idemp_l, Z.add_assoc.
  replace (base + bv_unsigned left + bv_unsigned right) with
    (base + (bv_unsigned left + bv_unsigned right - bv_modulus width) + bv_modulus width) by ring.
  rewrite bv_wrap_add_modulus_1.
  apply bv_wrap_small. exact Hrange.
Qed.

Ltac zesu_normalize_wrapped_findmem arithmetic :=
  lazymatch goal with
  | |- iris.proofmode.environments.envs_entails _ (find_in_context (FindMemMapsTo (bv_unsigned ?word)) _) =>
    lazymatch word with
    | bv_add (bv_add (Z_to_bv ?width ?base) ?left) ?right =>
      let Heq := fresh "HwrappedAddress" in
      assert (Heq : bv_unsigned word =
        base + (bv_unsigned left + bv_unsigned right - bv_modulus width)) by
        (apply zesu_wrapped_add_unsigned_small; arithmetic);
      rewrite Heq; clear Heq
    end
  end.

Ltac zesu_reduce_closed_Z_aliases_everywhere :=
  repeat match goal with
  | Hconstant : context [?scalar] |- _ =>
    let scalar_type := type of scalar in
    constr_eq scalar_type Z;
    is_closed_term scalar;
    let head := get_head scalar in
    constr_eq head scalar;
    assert_fails (is_var scalar);
    let reduced := eval cbv delta [scalar] in scalar in
    progress change scalar with reduced in *
  end.

Ltac zesu_wrapped_memory_lookup :=
  lazymatch goal with
  | |- iris.proofmode.environments.envs_entails _
      (find_in_context (FindMemMapsTo (bv_unsigned ?word)) _) =>
    lazymatch word with
    | bv_add (bv_add (Z_to_bv _ _) _) _ => idtac
    end
  end;
  ZesuSsz.Automation.PureFacts.zesu_saturate_derived_facts;
  repeat first [progress ZesuSsz.Automation.PureFacts.zesu_split_folded_pure |
    match goal with Hpair : _ /\ _ |- _ => destruct Hpair end];
  zesu_reduce_closed_Z_aliases_everywhere;
  zesu_normalize_wrapped_findmem ltac:(
    zesu_reduce_closed_Z_aliases; cbv [bv_unsigned bv_modulus] in *; lia);
  liStep.


