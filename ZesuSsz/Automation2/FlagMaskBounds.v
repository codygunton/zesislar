(* Pure bounds over comparison flags, size classes built from them, wrapped
   additions and low-bit masks. The step derives linear facts about the
   terms of the goal and closes it with lia on the facts that mention those
   terms. It names no address, offset or contract predicate. *)
From Coq Require Import ZArith.ZArith NArith.NArith Lia.
From stdpp Require Import base decidable bitvector.definitions bitvector.tactics.
From isla Require Import opsem.
Require Import ZesuSsz.Automation2.VmClosed.
Require Import ZesuSsz.Automation2.ContextCollection.
Local Open Scope Z_scope.

(* A 0/1 flag: a one-bit value from a condition, zero-extended. *)
Lemma zesu_flag_zero_extend (n : N) (c : bool) (one zero : bv 1) :
  (1 <= n)%N -> bv_unsigned one = 1 -> bv_unsigned zero = 0 ->
  (c = true /\ bv_unsigned (bv_zero_extend n (ite c one zero)) = 1) \/
  (c = false /\ bv_unsigned (bv_zero_extend n (ite c one zero)) = 0).
Proof.
  intros Hn Hone Hzero.
  destruct c; [left | right]; split; try reflexivity;
    rewrite bv_zero_extend_unsigned; assumption.
Qed.

Lemma zesu_flag_zero_extend_decide (n : N) (P : Prop) (HP : Decision P) (one zero : bv 1) :
  (1 <= n)%N -> bv_unsigned one = 1 -> bv_unsigned zero = 0 ->
  (P /\ bv_unsigned (bv_zero_extend n (ite (@bool_decide P HP) one zero)) = 1) \/
  (~ P /\ bv_unsigned (bv_zero_extend n (ite (@bool_decide P HP) one zero)) = 0).
Proof.
  intros Hn Hone Hzero.
  destruct (zesu_flag_zero_extend n (@bool_decide P HP) one zero Hn Hone Hzero)
    as [[Hc Hv] | [Hc Hv]]; [left | right]; split; try exact Hv.
  - by apply bool_decide_eq_true in Hc.
  - by apply bool_decide_eq_false in Hc.
Qed.

Lemma zesu_bit_zero_extend (n : N) (v : bv 1) :
  (1 <= n)%N ->
  bv_unsigned (bv_zero_extend n v) = bv_unsigned v /\ 0 <= bv_unsigned v <= 1.
Proof.
  intros Hn. rewrite bv_zero_extend_unsigned; [|exact Hn].
  pose proof (bv_unsigned_in_range 1 v) as Hrange.
  unfold bv_modulus in Hrange. simpl in Hrange. lia.
Qed.

(* xor with one on a 0/1 value is 1 - value. *)
Lemma zesu_xor_one_right (n : N) (t k : bv n) :
  bv_unsigned k = 1 ->
  0 <= bv_unsigned t <= 1 -> bv_unsigned (bv_xor t k) = 1 - bv_unsigned t.
Proof.
  intros Hk Ht. rewrite bv_xor_unsigned Hk.
  destruct (decide (bv_unsigned t = 0)) as [H0 | H1].
  - rewrite H0. reflexivity.
  - assert (Hone : bv_unsigned t = 1) by lia. rewrite Hone. reflexivity.
Qed.

Lemma zesu_xor_one_left (n : N) (k t : bv n) :
  bv_unsigned k = 1 ->
  0 <= bv_unsigned t <= 1 -> bv_unsigned (bv_xor k t) = 1 - bv_unsigned t.
Proof.
  intros Hk Ht. rewrite bv_xor_unsigned Z.lxor_comm -bv_xor_unsigned.
  apply zesu_xor_one_right; assumption.
Qed.

(* Unsigned subtraction and addition, split at the wrap point. *)
Lemma zesu_sub_cases (n : N) (modulus : Z) (left right : bv n) :
  modulus = bv_modulus n ->
  (bv_unsigned right <= bv_unsigned left ->
     bv_unsigned (bv_sub left right) = bv_unsigned left - bv_unsigned right) /\
  (bv_unsigned left < bv_unsigned right ->
     bv_unsigned (bv_sub left right) = bv_unsigned left - bv_unsigned right + modulus).
Proof.
  intros ->. pose proof (bv_unsigned_in_range n left). pose proof (bv_unsigned_in_range n right).
  rewrite bv_sub_unsigned. split; intros Hcase.
  - apply bv_wrap_small. lia.
  - rewrite -(bv_wrap_add_modulus 1 n) Z.mul_1_l. apply bv_wrap_small. lia.
Qed.

Lemma zesu_add_cases (n : N) (modulus : Z) (left right : bv n) :
  modulus = bv_modulus n ->
  (bv_unsigned left + bv_unsigned right < modulus ->
     bv_unsigned (bv_add left right) = bv_unsigned left + bv_unsigned right) /\
  (modulus <= bv_unsigned left + bv_unsigned right ->
     bv_unsigned (bv_add left right) = bv_unsigned left + bv_unsigned right - modulus).
Proof.
  intros ->. pose proof (bv_unsigned_in_range n left). pose proof (bv_unsigned_in_range n right).
  rewrite bv_add_unsigned. split; intros Hcase.
  - apply bv_wrap_small. lia.
  - rewrite -(bv_wrap_add_modulus (-1) n). apply bv_wrap_small. lia.
Qed.

Lemma zesu_unsigned_range (n : N) (modulus : Z) (value : bv n) :
  modulus = bv_modulus n -> 0 <= bv_unsigned value < modulus.
Proof. intros ->. apply bv_unsigned_in_range. Qed.

(* A low-bit mask 2^j - 1: the masked value is below 2^j, at most the source,
   and equal to the source when the source is below 2^j. *)
Lemma zesu_low_mask (n : N) (j limit : Z) (value mask : bv n) :
  0 <= j -> limit = 2 ^ j -> bv_unsigned mask = limit - 1 ->
  0 <= bv_unsigned (bv_and value mask) < limit /\
  bv_unsigned (bv_and value mask) <= bv_unsigned value /\
  (bv_unsigned value < limit -> bv_unsigned (bv_and value mask) = bv_unsigned value).
Proof.
  intros Hj -> Hmask.
  assert (Hones : bv_unsigned mask = Z.ones j) by (rewrite Z.ones_equiv; lia).
  pose proof (bv_unsigned_in_range n value).
  rewrite bv_and_unsigned Hones Z.land_ones; [|lia].
  split; [apply Z.mod_pos_bound; apply Z.pow_pos_nonneg; lia |].
  split; [apply Z.mod_le; [lia | apply Z.pow_pos_nonneg; lia] |].
  intros Hsmall. apply Z.mod_small. lia.
Qed.

Lemma zesu_low_mask_cast (n : N) (j limit modulus : Z) (source : Z) (mask : bv n) :
  0 <= j -> limit = 2 ^ j -> bv_unsigned mask = limit - 1 -> modulus = bv_modulus n ->
  limit <= modulus ->
  (0 <= source < limit ->
     bv_unsigned (bv_and (Z_to_bv n source) mask) = source).
Proof.
  intros Hj Hlimit Hmask Hmodulus Hle Hsource.
  destruct (zesu_low_mask n j limit (Z_to_bv n source) mask Hj Hlimit Hmask) as (_ & _ & Hvalue).
  rewrite Z_to_bv_small in Hvalue; [| lia]. apply Hvalue. lia.
Qed.

Lemma zesu_low_mask_zero_extend (n w : N) (j limit : Z) (source : bv w) (mask : bv n) :
  (w <= n)%N -> 0 <= j -> limit = 2 ^ j -> bv_unsigned mask = limit - 1 ->
  Z.leb (bv_modulus w) limit = true ->
  bv_unsigned (bv_and (bv_zero_extend n source) mask) = bv_unsigned source.
Proof.
  intros Hw Hj Hlimit Hmask Hle. apply Z.leb_le in Hle.
  destruct (zesu_low_mask n j limit (bv_zero_extend n source) mask Hj Hlimit Hmask) as (_ & _ & Hvalue).
  rewrite bv_zero_extend_unsigned in Hvalue; [| exact Hw].
  apply Hvalue. pose proof (bv_unsigned_in_range w source). lia.
Qed.

(* A cast of an integer in range keeps the integer. *)
Lemma zesu_cast_small (n : N) (modulus value : Z) :
  modulus = bv_modulus n ->
  (0 <= value < modulus -> bv_unsigned (Z_to_bv n value) = value).
Proof. intros -> Hrange. apply Z_to_bv_small. exact Hrange. Qed.

(* The step. Each fact is derived once per term of the goal. *)
Definition zesu_flag_seen {A : Type} (term : A) : Prop := True.

Ltac zesu_flag_unseen term :=
  assert_fails (idtac; match goal with
    | _ : zesu_flag_seen ?seen |- _ => constr_eq seen term
    end).

Ltac zesu_flag_mark term :=
  let H := fresh "HflagSeen" in
  assert (H : zesu_flag_seen term) by exact I.

(* Numerals for closed unsigned constants, so that lia reads them. *)
Ltac zesu_flag_numerals_in H :=
  repeat match type of H with
  | context [bv_unsigned ?constant] =>
      stdpp.tactics.is_closed_term constant;
      let value := eval vm_compute in (bv_unsigned constant) in
      change (bv_unsigned constant) with value in H
  end.

Ltac zesu_flag_numerals_goal :=
  repeat match goal with
  | |- context [bv_unsigned ?constant] =>
      stdpp.tactics.is_closed_term constant;
      let value := eval vm_compute in (bv_unsigned constant) in
      change (bv_unsigned constant) with value
  end.

Ltac zesu_flag_modulus n :=
  let _ := constr:(ltac:(stdpp.tactics.is_closed_term n; exact I) : True) in
  eval vm_compute in (bv_modulus n).

Ltac zesu_flag_range value :=
  lazymatch type of value with
  | bv ?n =>
      tryif stdpp.tactics.is_closed_term value then idtac else (
      zesu_flag_unseen (bv_unsigned value); zesu_flag_mark (bv_unsigned value);
      let modulus := zesu_flag_modulus n in
      let H := fresh "HflagRange" in
      pose proof (zesu_unsigned_range n modulus value ltac:(vm_compute; reflexivity)) as H)
  end.

(* Unfold the local definitions that the goal mentions. *)
Ltac zesu_flag_unfold_goal_locals :=
  repeat match goal with
  | |- context [?local] => is_var local; progress unfold local
  end.

Ltac zesu_flag_facts :=
  repeat match goal with
  | |- context [bv_zero_extend ?n (@ite (bv 1) (@bool_decide ?P ?HP) ?one ?zero)] =>
      let flag := constr:(bv_zero_extend n (@ite (bv 1) (@bool_decide P HP) one zero)) in
      zesu_flag_unseen flag; zesu_flag_mark flag;
      let H := fresh "HflagValue" in
      pose proof (zesu_flag_zero_extend_decide n P HP one zero ltac:(lia)
        ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)) as H
  | |- context [bv_zero_extend ?n (@ite (bv 1) ?c ?one ?zero)] =>
      let flag := constr:(bv_zero_extend n (@ite (bv 1) c one zero)) in
      zesu_flag_unseen flag; zesu_flag_mark flag;
      let H := fresh "HflagValue" in
      pose proof (zesu_flag_zero_extend n c one zero ltac:(lia)
        ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)) as H
  | |- context [bv_zero_extend ?n ?bit] =>
      lazymatch type of bit with bv 1 => idtac end;
      let flag := constr:(bv_zero_extend n bit) in
      zesu_flag_unseen flag; zesu_flag_mark flag;
      let H := fresh "HflagBit" in
      pose proof (zesu_bit_zero_extend n bit ltac:(lia)) as H
  end.

Ltac zesu_flag_xor_facts :=
  repeat match goal with
  | |- context [@bv_xor ?n ?left ?right] =>
      let term := constr:(@bv_xor n left right) in
      zesu_flag_unseen term; zesu_flag_mark term;
      let H := fresh "HflagXor" in
      first [
        stdpp.tactics.is_closed_term right;
        pose proof (zesu_xor_one_right n left right ltac:(vm_compute; reflexivity)) as H;
        zesu_flag_range left
      | stdpp.tactics.is_closed_term left;
        pose proof (zesu_xor_one_left n left right ltac:(vm_compute; reflexivity)) as H;
        zesu_flag_range right]
  end.

Ltac zesu_flag_wrap_facts :=
  repeat match goal with
  | |- context [@bv_sub ?n ?left ?right] =>
      let term := constr:(@bv_sub n left right) in
      zesu_flag_unseen term; zesu_flag_mark term;
      let modulus := zesu_flag_modulus n in
      let H := fresh "HflagSub" in
      pose proof (zesu_sub_cases n modulus left right ltac:(vm_compute; reflexivity)) as H;
      zesu_flag_numerals_in H;
      zesu_flag_range left; zesu_flag_range right
  | |- context [@bv_add ?n ?left ?right] =>
      let term := constr:(@bv_add n left right) in
      zesu_flag_unseen term; zesu_flag_mark term;
      let modulus := zesu_flag_modulus n in
      let H := fresh "HflagAdd" in
      pose proof (zesu_add_cases n modulus left right ltac:(vm_compute; reflexivity)) as H;
      zesu_flag_numerals_in H;
      zesu_flag_range left; zesu_flag_range right
  end.

Ltac zesu_flag_mask_width mask :=
  let value := eval vm_compute in (bv_unsigned mask) in
  let width := eval vm_compute in (Z.log2 (value + 1)) in
  lazymatch eval vm_compute in (Z.eqb (2 ^ width) (value + 1)) with true => width end.

Ltac zesu_flag_mask_facts :=
  repeat match goal with
  | |- context [@bv_and ?n ?source ?mask] =>
      stdpp.tactics.is_closed_term mask;
      let term := constr:(@bv_and n source mask) in
      zesu_flag_unseen term; zesu_flag_mark term;
      let width := zesu_flag_mask_width mask in
      let limit := eval vm_compute in (2 ^ width) in
      let H := fresh "HflagMask" in
      pose proof (zesu_low_mask n width limit source mask ltac:(lia)
        ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)) as H;
      zesu_flag_range source;
      try (lazymatch source with
      | Z_to_bv _ ?value =>
          let modulus := zesu_flag_modulus n in
          let Hcast := fresh "HflagMaskCast" in
          pose proof (zesu_low_mask_cast n width limit modulus value mask ltac:(lia)
            ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)
            ltac:(vm_compute; reflexivity) ltac:(lia)) as Hcast
      | @bv_zero_extend ?w _ ?inner =>
          let Hcast := fresh "HflagMaskCast" in
          pose proof (zesu_low_mask_zero_extend n w width limit inner mask
            ltac:(lia) ltac:(lia) ltac:(vm_compute; reflexivity)
            ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)) as Hcast
      end)
  end.

(* A cast of an open integer: its value when the integer is in range. *)
Ltac zesu_flag_cast_facts :=
  repeat match goal with
  | |- context [@Z_to_bv ?n ?value] =>
      tryif stdpp.tactics.is_closed_term value then fail else idtac;
      let term := constr:(@Z_to_bv n value) in
      zesu_flag_unseen term; zesu_flag_mark term;
      let modulus := zesu_flag_modulus n in
      let H := fresh "HflagCast" in
      pose proof (zesu_cast_small n modulus value ltac:(vm_compute; reflexivity)) as H
  end.

(* A remainder by a closed positive divisor, as a linear equation over the
   quotient and the remainder, and each divisibility fact by a closed divisor
   as an equation over its quotient. *)
Ltac zesu_flag_modulo_facts :=
  repeat match goal with
  | |- context [Z.modulo ?value ?divisor] =>
      stdpp.tactics.is_closed_term divisor;
      lazymatch eval vm_compute in (0 <? divisor)%Z with true => idtac end;
      let term := constr:(Z.modulo value divisor) in
      zesu_flag_unseen term; zesu_flag_mark term;
      let Hequation := fresh "HflagDivMod" in
      let Hbound := fresh "HflagModBound" in
      pose proof (Z.div_mod value divisor ltac:(lia)) as Hequation;
      pose proof (Z.mod_pos_bound value divisor ltac:(lia)) as Hbound
  end;
  repeat match goal with
  | Hdivide : Z.divide ?divisor ?value |- _ =>
      stdpp.tactics.is_closed_term divisor;
      let term := constr:(Z.divide divisor value) in
      zesu_flag_unseen term; zesu_flag_mark term;
      let quotient := fresh "flagQuotient" in
      let Hquotient := fresh "HflagQuotient" in
      destruct Hdivide as [quotient Hquotient]
  end.

Ltac zesu_flag_divisibility_shape :=
  lazymatch goal with
  | |- context [Z.modulo _ ?divisor] =>
      stdpp.tactics.is_closed_term divisor;
      lazymatch goal with _ : Z.divide _ _ |- _ => idtac end
  end.

(* A remainder by a closed divisor, before any divisibility fact is in the
   context: the divisibility may still be folded behind a registered
   derivation. *)
Ltac zesu_flag_remainder_goal :=
  lazymatch goal with
  | |- context [Z.modulo _ ?divisor] => stdpp.tactics.is_closed_term divisor
  end.

(* Derived ranges state their bound as `bv_modulus n`; lia reads it as an
   atom. Evaluate each closed modulus in the hypotheses. *)
Ltac zesu_flag_closed_moduli :=
  repeat match goal with
  | H : context [bv_modulus ?width] |- _ =>
      stdpp.tactics.is_closed_term width;
      let value := eval vm_compute in (bv_modulus width) in
      change (bv_modulus width) with value in H
  end.

Ltac zesu_flag_goal_head :=
  lazymatch goal with
  | |- (_ < _)%Z => idtac
  | |- (_ <= _)%Z => idtac
  | |- (_ <= _ < _)%Z => idtac
  | |- (_ < _ < _)%Z => idtac
  | |- (_ < _ <= _)%Z => idtac
  | |- @eq Z _ _ => idtac
  end.

Ltac zesu_flag_shape_in term :=
  lazymatch term with
  | context [bv_zero_extend _ (@ite (bv 1) _ _ _)] => idtac
  | context [@bv_and _ (Z_to_bv _ _) _] => idtac
  | context [@bv_and _ (bv_zero_extend _ _) _] => idtac
  end.

(* The shape may sit in a local definition that the goal mentions, up to
   three definitions deep. Nothing is unfolded before the shape is found. *)
Ltac zesu_flag_shape_deep term depth :=
  first [zesu_flag_shape_in term |
    lazymatch depth with
    | S ?rest =>
        match term with
        | context [?local] =>
            is_var local;
            let body := eval cbv delta [local] in local in
            tryif constr_eq body local then fail else zesu_flag_shape_deep body rest
        end
    end].

Ltac zesu_flag_shape :=
  first [lazymatch goal with
    | |- ?goal => zesu_flag_shape_deep goal 3%nat
    end
  | zesu_flag_divisibility_shape].

(* A pure bound over a comparison flag or a low-bit mask of a cast, or a
   remainder by a closed divisor when the context states a divisibility. *)
Ltac zesu_flag_mask_bound :=
  zesu_flag_goal_head;
  zesu_flag_shape;
  zesu_flag_unfold_goal_locals;
  zesu_flag_facts; zesu_flag_xor_facts; zesu_flag_mask_facts; zesu_flag_wrap_facts;
  zesu_flag_cast_facts; zesu_flag_modulo_facts;
  zesu_flag_numerals_goal;
  repeat match goal with H : zesu_flag_seen _ |- _ => clear H end;
  ZesuSsz.Automation2.ContextCollection.zesu_solve_goal_selected
    ("flag_mask_bound"%string) ltac:(lia).
