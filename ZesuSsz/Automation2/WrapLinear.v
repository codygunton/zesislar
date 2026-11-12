(* Wrap-to-linear for bounds (W1b).

   For a bit-vector term t built from sums, differences and casts, W1a gives
   bv_unsigned t = bv_wrap n P. With each coefficient and the constant of P
   reduced to its centered residue modulo 2^n (2^64 - 96 becomes -96), the
   canonical form L agrees with P modulo 2^n, so bv_unsigned t = L when
   0 <= L < 2^n. The step poses that equation with L as a plain linear term.
   When that range does not follow, t may equal bv_unsigned a + d for a
   wrapped term a that the context bounds (anchored form); a remainder by a
   divisor of 2^n is linear with no range at all.

   Ranges are proved at the block cache step only (once per term and block),
   which poses the equations in the main context; a solver call rewrites with
   them and linearizes remainders, which need no range.

   The range proof is one linear call on the facts linked to the goal. Inside
   that proof only, it reads signed comparisons of zero-extended values into
   unsigned facts, adds the quotient equation of each wrapped operand of those
   comparisons, and adds the bounds of the unsigned atoms.

   Bounded by count: 8 candidates, 8 range solver calls, 16 read hypotheses,
   4 anchors per call. Only closed syntax goes to vm_compute. *)
From Coq Require Import ZArith List Lia Bool Znumtheory.
From Coq Require Import micromega.Zify.
From stdpp Require Import tactics bitvector.definitions.
Require Import ZesuSsz.Automation2.VmClosed.
Require Import ZesuSsz.Automation2.BvLinear.
Require Import ZesuSsz.Automation2.LinearFirstLia.
Import ListNotations.
Local Open Scope Z_scope.

(* ---- Canonical form. ---- *)

Definition zesu_centered (modulus value : Z) : Z :=
  if modulus <? 2 * (value mod modulus) then value mod modulus - modulus
  else value mod modulus.

Definition zesu_bvlin_canon (width : N) (poly : zesuLinPoly) : zesuLinPoly :=
  (zesu_centered (bv_modulus width) (fst poly),
   map (fun entry => (fst entry, zesu_centered (bv_modulus width) (snd entry))) (snd poly)).

Definition zesu_bvlin_linear_form (width : N) (term : zesuBvLin) : option zesuLinPoly :=
  match zesuBvNorm width term with
  | Some poly => Some (zesu_bvlin_canon width poly)
  | None => None
  end.

(* A constant d with term = anchor + d modulo 2^width. Only a choice: the
   anchored equation is proved by W1a's equality check. *)
Definition zesu_bvlin_offset (width : N) (term anchor : zesuBvLin) : option Z :=
  match zesuBvNorm width term, zesuBvNorm width anchor with
  | Some p, Some q =>
      let difference := zesuPolyAdd p (zesuPolyNeg q) in
      if zesuTermsZeroMod (bv_modulus width) (snd difference)
      then Some (zesu_centered (bv_modulus width) (fst difference)) else None
  | _, _ => None
  end.

(* A term whose range failed at a cache step, with the context size then.
   Sort Type: Prop selections and solvers never keep it. *)
Inductive zesu_wrap_refused {A : Type} (term : A) (size : nat) : Type :=
  zesu_wrap_refused_intro.

Lemma zesu_centered_congr modulus value :
  0 < modulus -> exists k, zesu_centered modulus value = value + k * modulus.
Proof.
  intros Hpos. unfold zesu_centered.
  rewrite (Z.mod_eq value modulus) by lia.
  match goal with |- context [if ?c then _ else _] => destruct c end.
  - exists (- (value / modulus) - 1). ring.
  - exists (- (value / modulus)). ring.
Qed.

Section wrap_denote.
Context {width : N} (atoms : list (bv width)) (integers : list Z).

Lemma zesu_bvlin_terms_canon_congr modulus terms :
  0 < modulus ->
  exists k, zesuTermsEval atoms integers
      (map (fun entry => (fst entry, zesu_centered modulus (snd entry))) terms) =
    zesuTermsEval atoms integers terms + k * modulus.
Proof.
  intros Hpos. induction terms as [|[key coeff] rest [k IH]];
    cbn [zesuTermsEval map fst snd].
  - exists 0. ring.
  - destruct (zesu_centered_congr modulus coeff Hpos) as [j Hj].
    rewrite Hj, IH. exists (j * zesuKeyValue atoms integers key + k). ring.
Qed.

Lemma zesu_bvlin_canon_congr poly :
  exists k, zesuPolyEval atoms integers (zesu_bvlin_canon width poly) =
    zesuPolyEval atoms integers poly + k * bv_modulus width.
Proof.
  pose proof (bv_modulus_pos width) as Hpos.
  destruct poly as [constant terms]. unfold zesu_bvlin_canon, zesuPolyEval. cbn [fst snd].
  destruct (zesu_centered_congr (bv_modulus width) constant Hpos) as [j Hj].
  destruct (zesu_bvlin_terms_canon_congr (bv_modulus width) terms Hpos) as [k Hk].
  rewrite Hj, Hk. exists (j + k). ring.
Qed.
End wrap_denote.

(* The spec's soundness lemma. *)
Lemma zesu_bvlin_unsigned_linear {width : N} (atoms literals : list (bv width))
    (integers : list Z) (term : zesuBvLin) (poly : zesuLinPoly) :
  zesuBvLinLitCheck literals term = true ->
  zesuBvNorm width term = Some poly ->
  0 <= zesuPolyEval atoms integers (zesu_bvlin_canon width poly) < bv_modulus width ->
  bv_unsigned (zesuBvLinDenote atoms literals integers term) =
    zesuPolyEval atoms integers (zesu_bvlin_canon width poly).
Proof.
  intros Hlit Hnorm Hrange.
  pose proof (bv_modulus_pos width) as Hpos.
  rewrite (zesuBvNorm_sound atoms literals integers term poly Hlit Hnorm).
  destruct (zesu_bvlin_canon_congr atoms integers poly) as [k Hk].
  rewrite <- (bv_wrap_small width _ Hrange).
  unfold bv_wrap. rewrite Hk. symmetry. apply Z.mod_add. lia.
Qed.

(* Tactic forms: the term and the readable value are explicit. *)
Lemma zesu_bvlin_unsigned_linear_at {width : N} (atoms literals : list (bv width))
    (integers : list Z) (term : bv width) (syntax : zesuBvLin) (cpoly : zesuLinPoly)
    (value : Z) :
  zesuBvLinDenote atoms literals integers syntax = term ->
  zesuBvLinLitCheck literals syntax = true ->
  zesu_bvlin_linear_form width syntax = Some cpoly ->
  zesuPolyEval atoms integers cpoly = value ->
  0 <= value < bv_modulus width ->
  bv_unsigned term = value.
Proof.
  intros <- Hlit Hform <- Hrange.
  unfold zesu_bvlin_linear_form in Hform.
  destruct (zesuBvNorm width syntax) as [poly|] eqn:Hnorm; [|discriminate].
  inversion Hform; subst.
  exact (zesu_bvlin_unsigned_linear atoms literals integers syntax poly Hlit Hnorm Hrange).
Qed.

Lemma zesu_bvlin_unsigned_quotient_at {width : N} (atoms literals : list (bv width))
    (integers : list Z) (term : bv width) (syntax : zesuBvLin) (cpoly : zesuLinPoly)
    (value modulus : Z) :
  zesuBvLinDenote atoms literals integers syntax = term ->
  zesuBvLinLitCheck literals syntax = true ->
  zesu_bvlin_linear_form width syntax = Some cpoly ->
  zesuPolyEval atoms integers cpoly = value ->
  bv_modulus width = modulus ->
  exists quotient, bv_unsigned term = value - modulus * quotient.
Proof.
  intros <- Hlit Hform <- <-.
  unfold zesu_bvlin_linear_form in Hform.
  destruct (zesuBvNorm width syntax) as [poly|] eqn:Hnorm; [|discriminate].
  inversion Hform; subst.
  pose proof (bv_modulus_pos width) as Hpos.
  assert (Hne : bv_modulus width <> 0) by lia.
  destruct (zesu_bvlin_canon_congr atoms integers poly) as [k Hk].
  rewrite (zesuBvNorm_sound atoms literals integers syntax poly Hlit Hnorm).
  rewrite Hk.
  exists ((zesuPolyEval atoms integers poly + k * bv_modulus width) / bv_modulus width).
  unfold bv_wrap.
  rewrite <- (Z.mod_add (zesuPolyEval atoms integers poly) k (bv_modulus width) Hne).
  apply Z.mod_eq. exact Hne.
Qed.

Lemma zesu_bvlin_unsigned_mod_at {width : N} (atoms literals : list (bv width))
    (integers : list Z) (term : bv width) (syntax : zesuBvLin) (cpoly : zesuLinPoly)
    (value divisor : Z) :
  zesuBvLinDenote atoms literals integers syntax = term ->
  zesuBvLinLitCheck literals syntax = true ->
  zesu_bvlin_linear_form width syntax = Some cpoly ->
  zesuPolyEval atoms integers cpoly = value ->
  0 < divisor -> bv_modulus width mod divisor = 0 ->
  bv_unsigned term mod divisor = value mod divisor.
Proof.
  intros <- Hlit Hform <- Hdivisor Hmodulus.
  unfold zesu_bvlin_linear_form in Hform.
  destruct (zesuBvNorm width syntax) as [poly|] eqn:Hnorm; [|discriminate].
  inversion Hform; subst.
  pose proof (bv_modulus_pos width) as Hpos.
  assert (Hdivides : (divisor | bv_modulus width)).
  { apply Z.mod_divide; [lia | exact Hmodulus]. }
  destruct (zesu_bvlin_canon_congr atoms integers poly) as [k Hk].
  rewrite (zesuBvNorm_sound atoms literals integers syntax poly Hlit Hnorm).
  rewrite Hk. unfold bv_wrap.
  rewrite <- (Zmod_div_mod divisor (bv_modulus width) (zesuPolyEval atoms integers poly)
    Hdivisor Hpos Hdivides).
  destruct Hdivides as [j Hj].
  rewrite Hj. rewrite Z.mul_assoc. symmetry. apply Z.mod_add. lia.
Qed.

Lemma zesu_wrap_anchor {width : N} (term anchor : bv width) (offset value : Z) :
  term = bv_add anchor (Z_to_bv width offset) ->
  bv_unsigned anchor + offset = value ->
  0 <= value < bv_modulus width ->
  bv_unsigned term = value.
Proof.
  intros -> <- Hrange.
  rewrite bv_add_unsigned. rewrite Z_to_bv_unsigned.
  unfold bv_wrap. rewrite Zplus_mod_idemp_r. apply Z.mod_small. exact Hrange.
Qed.

Lemma zesu_wrap_signed_zero_extend (n m : N) (value : bv n) :
  bv_modulus n <= bv_half_modulus m ->
  bv_signed (bv_zero_extend m value) = bv_unsigned value.
Proof.
  intros Hsmall. pose proof (bv_unsigned_in_range n value) as Hrange.
  rewrite bv_zero_extend_signed. apply bv_swrap_small. lia.
Qed.

Lemma zesu_wrap_signed_zero_extend_add (n m : N) (value : bv n) (offset : bv m)
    (constant : Z) :
  (n <= m)%N -> bv_unsigned offset = constant -> 0 <= constant ->
  bv_modulus n + constant <= bv_half_modulus m ->
  bv_signed (bv_add (bv_zero_extend m value) offset) = bv_unsigned value + constant.
Proof.
  intros Hwidth Hoffset Hnonneg Hsmall.
  pose proof (bv_unsigned_in_range n value) as Hrange.
  pose proof (bv_modulus_pos m) as Hpos.
  assert (Hhalf : bv_half_modulus m <= bv_modulus m).
  { unfold bv_half_modulus. apply Z.div_le_upper_bound; lia. }
  unfold bv_signed. rewrite bv_add_unsigned.
  rewrite (bv_zero_extend_unsigned m value Hwidth). rewrite Hoffset.
  rewrite (bv_wrap_small m (bv_unsigned value + constant)) by lia.
  apply bv_swrap_small. lia.
Qed.

Lemma zesu_wrap_unsigned_bounds (width : N) (modulus : Z) (value : bv width) :
  bv_modulus width = modulus -> 0 <= bv_unsigned value < modulus.
Proof. intros <-. apply bv_unsigned_in_range. Qed.

(* ---- Ltac1 steps (closed premises go to zesu_vm_closed_decide). ---- *)

Ltac zesu_wrap_close_check :=
  ZesuSsz.Automation2.VmClosed.zesu_vm_compute_closed; reflexivity.

Ltac zesu_wrap_eval_step :=
  cbv [zesuPolyEval zesuTermsEval zesuKeyValue nth fst snd]; ring.

Ltac zesu_wrap_read_signed_term signed :=
  lazymatch signed with
  | @bv_signed _ (@bv_add _ (@bv_zero_extend ?source ?target ?value) ?offset) =>
      zesu_vm_closed offset;
      let constant := zesu_vm_eval_closed (bv_unsigned offset) in
      pose proof (zesu_wrap_signed_zero_extend_add source target value offset constant
        ltac:(zesu_vm_closed_decide) ltac:(zesu_vm_closed_decide)
        ltac:(zesu_vm_closed_decide) ltac:(zesu_vm_closed_decide))
  | @bv_signed _ (@bv_zero_extend ?source ?target ?value) =>
      pose proof (zesu_wrap_signed_zero_extend source target value
        ltac:(zesu_vm_closed_decide))
  | @bv_signed ?width ?constant =>
      zesu_vm_closed constant;
      let result := zesu_vm_eval_closed (@bv_signed width constant) in
      let Hsigned := fresh "HwrapSigned" in
      assert (Hsigned : @bv_signed width constant = result) by zesu_vm_closed_decide
  end.

Ltac zesu_wrap_pose_bounds width value :=
  let modulus := zesu_vm_eval_closed (bv_modulus width) in
  pose proof (zesu_wrap_unsigned_bounds width modulus value ltac:(zesu_vm_closed_decide)).

Ltac zesu_wrap_pose_quotient width term value reified atoms literals integers cpoly :=
  let modulus := zesu_vm_eval_closed (bv_modulus width) in
  let quotient := fresh "wrapQuotient" in
  let Hquotient := fresh "HwrapQuotient" in
  destruct (@zesu_bvlin_unsigned_quotient_at width atoms literals integers term reified
      cpoly value modulus ltac:(reflexivity) ltac:(zesu_wrap_close_check)
      ltac:(zesu_wrap_close_check) ltac:(zesu_wrap_eval_step) ltac:(zesu_vm_closed_decide))
    as [quotient Hquotient].

Ltac zesu_wrap_pose_linear name width term value reified atoms literals integers cpoly range :=
  assert (name : @bv_unsigned width term = value) by
    (refine (@zesu_bvlin_unsigned_linear_at width atoms literals integers term reified cpoly
       value _ _ _ _ range);
     [reflexivity | zesu_wrap_close_check | zesu_wrap_close_check | zesu_wrap_eval_step]);
  clear range.

Ltac zesu_wrap_pose_anchor name width term anchor offset value range :=
  assert (name : @bv_unsigned width term = value) by
    (refine (@zesu_wrap_anchor width term anchor offset value _ _ range);
     [zesu_bv_linear_bv | ring]);
  clear range.

Ltac zesu_wrap_pose_mod name width term value reified atoms literals integers cpoly divisor :=
  assert (name : Z.modulo (@bv_unsigned width term) divisor = Z.modulo value divisor) by
    (refine (@zesu_bvlin_unsigned_mod_at width atoms literals integers term reified cpoly
       value divisor _ _ _ _ _ _);
     [reflexivity | zesu_wrap_close_check | zesu_wrap_close_check | zesu_wrap_eval_step
     | zesu_vm_closed_decide | zesu_vm_closed_decide]).

(* Each divisibility by a closed divisor as an equation over its quotient,
   when the goal has a remainder by a closed divisor. *)
Ltac zesu_wrap_divisibility :=
  match goal with |- context [Z.modulo _ ?divisor] => zesu_vm_closed divisor end;
  progress (repeat match goal with
  | Hdivide : Z.divide ?divisor _ |- _ =>
      zesu_vm_closed divisor;
      let quotient := fresh "wrapQuotient" in
      let Hquotient := fresh "HwrapDivide" in
      destruct Hdivide as [quotient Hquotient]
  end).

Ltac zesu_wrap_goal_head :=
  lazymatch goal with |- ?goal => assert_fails (has_evar goal) end;
  lazymatch goal with
  | |- @eq Z _ _ => idtac | |- not _ => idtac
  | |- Z.le _ _ => idtac | |- Z.lt _ _ => idtac
  | |- Z.ge _ _ => idtac | |- Z.gt _ _ => idtac
  | |- and _ _ => idtac | |- or _ _ => idtac
  end.

(* ---- Ltac2: candidates, forms, ranges. ---- *)

From Ltac2 Require Import Ltac2.
Set Default Proof Mode "Classic".

(* One linear call on the facts linked to the goal; no division branch. *)
Ltac zesu_wrap_range_solver :=
  zesu_bv_modulus_value;
  try (once ltac2:(zesu_linear_clear_unrelated ()));
  zesu_zify_prefix; Zify.zify_saturate; xlia Lia.zchecker.

Ltac2 zesu_wrap_attempt (tac : unit -> unit) : bool :=
  match Control.case tac with
  | Val _ => true
  | Err _ => false
  end.

Ltac2 zesu_wrap_wrapping (term : constr) : bool :=
  lazy_match! term with
  | bv_add _ _ => true
  | bv_sub _ _ => true
  | Z_to_bv _ _ => true
  | _ => false
  end.

(* One walk: bv_unsigned of a wrapping term with no evar, no bound variable,
   not closed; at most cap. *)
Ltac2 rec zesu_wrap_walk (unsigned : constr) (cap : int) (term : constr)
    (found : (constr * constr) list) : (constr * constr) list :=
  if Int.ge (List.length found) cap then found else
  match Constr.Unsafe.kind term with
  | Constr.Unsafe.App head args =>
      let found :=
        if Bool.and (Constr.equal head unsigned) (Int.equal (Array.length args) 2) then
          let inner := Array.get args 1 in
          if Bool.or (Bool.neg (Constr.Unsafe.is_closed inner)) (Constr.has_evar inner)
          then found
          else if Bool.neg (zesu_wrap_wrapping inner) then found
          else if List.exist (fun c => let (_, t) := c in Constr.equal t inner) found
          then found
          else if zesu_bvlin_closed inner then found
          else List.append found [(Array.get args 0, inner)]
        else found in
      Array.fold_left (fun acc arg => zesu_wrap_walk unsigned cap arg acc) found args
  | Constr.Unsafe.Prod binder body =>
      zesu_wrap_walk unsigned cap body
        (zesu_wrap_walk unsigned cap (Constr.Binder.type binder) found)
  | Constr.Unsafe.Lambda binder body =>
      zesu_wrap_walk unsigned cap body
        (zesu_wrap_walk unsigned cap (Constr.Binder.type binder) found)
  | Constr.Unsafe.Cast body _ _ => zesu_wrap_walk unsigned cap body found
  | _ => found
  end.

Ltac2 zesu_wrap_candidates (term : constr) : (constr * constr) list :=
  zesu_wrap_walk constr:(@bv_unsigned) 8 term [].

(* Outermost applications of head, at most cap. *)
Ltac2 rec zesu_wrap_collect (head : constr) (cap : int) (term : constr)
    (found : constr list) : constr list :=
  if Int.ge (List.length found) cap then found else
  match Constr.Unsafe.kind term with
  | Constr.Unsafe.App f args =>
      if Constr.equal f head then
        if Bool.or (Bool.neg (Constr.Unsafe.is_closed term))
             (List.exist (Constr.equal term) found)
        then found else List.append found [term]
      else Array.fold_left (fun acc arg => zesu_wrap_collect head cap arg acc) found args
  | Constr.Unsafe.Prod binder body =>
      zesu_wrap_collect head cap body
        (zesu_wrap_collect head cap (Constr.Binder.type binder) found)
  | Constr.Unsafe.Cast body _ _ => zesu_wrap_collect head cap body found
  | _ => found
  end.

Ltac2 rec zesu_wrap_occurs (needle : constr) (term : constr) : bool :=
  if Constr.equal needle term then true else
  match Constr.Unsafe.kind term with
  | Constr.Unsafe.App _ args =>
      Array.fold_left (fun seen arg => if seen then true else zesu_wrap_occurs needle arg)
        false args
  | Constr.Unsafe.Cast body _ _ => zesu_wrap_occurs needle body
  | _ => false
  end.

Ltac2 rec zesu_wrap_nat (n : constr) : int :=
  lazy_match! n with
  | S ?m => Int.add 1 (zesu_wrap_nat m)
  | _ => 0
  end.

(* The readable right side: atoms with coefficients 1 or -1 bare, the
   constant last as + c or - c. *)
Ltac2 zesu_wrap_monomial (magnitude : constr) (atom : constr) : constr :=
  lazy_match! magnitude with
  | Zpos xH => atom
  | _ => constr:(Z.mul $magnitude $atom)
  end.

Ltac2 zesu_wrap_push (sum : constr option) (coeff : constr) (atom : constr) : constr option :=
  lazy_match! coeff with
  | Zpos ?p =>
      let term := zesu_wrap_monomial constr:(Zpos $p) atom in
      match sum with
      | None => Some term
      | Some s => Some constr:(Z.add $s $term)
      end
  | Zneg ?p =>
      let term := zesu_wrap_monomial constr:(Zpos $p) atom in
      match sum with
      | None => Some constr:(Z.opp $term)
      | Some s => Some constr:(Z.sub $s $term)
      end
  | _ => sum
  end.

Ltac2 zesu_wrap_close_sum (sum : constr option) (constant : constr) : constr :=
  match sum with
  | None => constant
  | Some s =>
      lazy_match! constant with
      | Zpos ?p => constr:(Z.add $s (Zpos $p))
      | Zneg ?p => constr:(Z.sub $s (Zpos $p))
      | _ => s
      end
  end.

Ltac2 rec zesu_wrap_sum (width : constr) (bvs : constr list) (zs : constr list)
    (terms : constr) (sum : constr option) : constr option :=
  lazy_match! terms with
  | cons (pair (pair ?kind ?index) ?coeff) ?rest =>
      let position := zesu_wrap_nat index in
      let atom := lazy_match! kind with
        | true => let a := List.nth bvs position in constr:(@bv_unsigned $width $a)
        | _ => List.nth zs position
        end in
      zesu_wrap_sum width bvs zs rest (zesu_wrap_push sum coeff atom)
  | _ => sum
  end.

Ltac2 zesu_wrap_value (width : constr) (bvs : constr list) (zs : constr list)
    (cpoly : constr) : constr :=
  lazy_match! cpoly with
  | pair ?constant ?terms =>
      zesu_wrap_close_sum (zesu_wrap_sum width bvs zs terms None) constant
  end.

Ltac2 Type zesu_wrap_reified := {
  wf_syntax : constr; wf_atoms : constr; wf_literals : constr; wf_integers : constr;
  wf_bvs : constr list; wf_zs : constr list; wf_cpoly : constr; wf_value : constr }.

Ltac2 zesu_wrap_form (width : constr) (term : constr) : zesu_wrap_reified option :=
  let state := { bv_atoms := []; bv_literals := []; z_atoms := [] } in
  let syntax := zesu_bvlin_reify width state term in
  let query := constr:(zesu_bvlin_linear_form $width $syntax) in
  if zesu_bvlin_closed query then
    let result := Std.eval_vm None query in
    lazy_match! result with
    | Some ?cpoly =>
        let kind := constr:(bv $width) in
        let bvs := state.(bv_atoms) in
        let zs := state.(z_atoms) in
        Some { wf_syntax := syntax; wf_atoms := zesu_bvlin_list kind bvs;
               wf_literals := zesu_bvlin_list kind (state.(bv_literals));
               wf_integers := zesu_bvlin_list constr:(Z) zs; wf_bvs := bvs; wf_zs := zs;
               wf_cpoly := cpoly; wf_value := zesu_wrap_value width bvs zs cpoly }
    | _ => None
    end
  else None.

Ltac2 zesu_wrap_offset (width : constr) (term : constr) (anchor : constr) : constr option :=
  let state := { bv_atoms := []; bv_literals := []; z_atoms := [] } in
  let left := zesu_bvlin_reify width state term in
  let right := zesu_bvlin_reify width state anchor in
  let query := constr:(zesu_bvlin_offset $width $left $right) in
  if zesu_bvlin_closed query then
    let result := Std.eval_vm None query in
    lazy_match! result with
    | Some ?offset => Some offset
    | _ => None
    end
  else None.

(* Terms with an equation (its name) or a refusal. A solver call honours a
   refusal only while the context has the size it had at the refusal. *)
Ltac2 zesu_wrap_known (strict : bool) : (constr * ident option) list :=
  let hyps := Control.hyps () in
  let size := List.length hyps in
  List.fold_left (fun known declaration =>
    let (name, body, statement) := declaration in
    match body with
    | Some _ => known
    | None =>
        lazy_match! statement with
        | @eq Z (@bv_unsigned _ ?t) _ => (t, Some name) :: known
        | @eq Z (Z.modulo (@bv_unsigned _ ?t) _) _ => (t, None) :: known
        | zesu_wrap_refused ?t ?n =>
            if Bool.or strict (Int.equal (zesu_wrap_nat n) size) then (t, None) :: known
            else known
        | _ => known
        end
    end) [] hyps.

(* bv_signed subterms per hypothesis, newest first, at most 16 hypotheses. *)
Ltac2 zesu_wrap_signed_groups () : constr list list :=
  let head := constr:(@bv_signed) in
  List.fold_left (fun groups declaration =>
    if Int.ge (List.length groups) 16 then groups else
    let (_, body, statement) := declaration in
    match body with
    | Some _ => groups
    | None =>
        match zesu_wrap_collect head 8 statement [] with
        | [] => groups
        | signed => signed :: groups
        end
    end) [] (List.rev (Control.hyps ())).

Ltac2 zesu_wrap_relevant (groups : constr list list) (atoms : constr list) : constr list :=
  List.fold_left (fun read group =>
    if List.exist (fun signed => List.exist (fun atom => zesu_wrap_occurs atom signed) atoms)
         group
    then List.fold_left (fun read signed =>
           if List.exist (Constr.equal signed) read then read else List.append read [signed])
           read group
    else read) [] groups.

Ltac2 zesu_wrap_operand (signed : constr) : constr option :=
  lazy_match! signed with
  | bv_signed (bv_add (bv_zero_extend _ ?w) _) => Some w
  | bv_signed (bv_zero_extend _ ?w) => Some w
  | _ => None
  end.

Ltac2 zesu_wrap_anchors (width : constr) (read : constr list) : constr list :=
  let kind := constr:(bv $width) in
  List.fold_left (fun anchors signed =>
    if Int.ge (List.length anchors) 4 then anchors else
    match zesu_wrap_operand signed with
    | Some w =>
        if List.exist (Constr.equal w) anchors then anchors
        else if Bool.neg (zesu_wrap_wrapping w) then anchors
        else if Constr.equal (Constr.type w) kind then List.append anchors [w]
        else anchors
    | None => anchors
    end) [] read.

Ltac2 Type zesu_wrap_budget := {
  mutable wb_left : int; mutable wb_groups : constr list list option }.

Ltac2 zesu_wrap_groups (budget : zesu_wrap_budget) : constr list list :=
  match budget.(wb_groups) with
  | Some groups => groups
  | None =>
      let groups := zesu_wrap_signed_groups () in
      (budget.(wb_groups) := Some groups; groups)
  end.

Ltac2 zesu_wrap_assert (name : ident) (statement : constr) (tac : unit -> unit) : bool :=
  zesu_wrap_attempt (fun () =>
    Std.assert (Std.AssertType (Some (Std.IntroNaming (Std.IntroIdentifier name)))
      statement (Some tac))).

(* Facts for one range proof; every pose is local to that proof. *)
Ltac2 zesu_wrap_prepare_range (width : constr) (bvs : constr list) (read : constr list)
    (anchors : constr list) : unit :=
  List.iter (fun signed =>
    let _ := zesu_wrap_attempt (fun () =>
      ltac1:(s0 |- zesu_wrap_read_signed_term s0) (Ltac1.of_constr signed)) in ()) read;
  let bvs := List.fold_left (fun bvs anchor =>
    match zesu_wrap_form width anchor with
    | Some f =>
        let _ := zesu_wrap_attempt (fun () =>
          ltac1:(w0 t0 v0 r0 a0 l0 i0 c0 |- zesu_wrap_pose_quotient w0 t0 v0 r0 a0 l0 i0 c0)
            (Ltac1.of_constr width) (Ltac1.of_constr anchor) (Ltac1.of_constr (f.(wf_value)))
            (Ltac1.of_constr (f.(wf_syntax))) (Ltac1.of_constr (f.(wf_atoms)))
            (Ltac1.of_constr (f.(wf_literals))) (Ltac1.of_constr (f.(wf_integers)))
            (Ltac1.of_constr (f.(wf_cpoly)))) in
        List.fold_left (fun bvs b =>
          if List.exist (Constr.equal b) bvs then bvs else List.append bvs [b])
          bvs (f.(wf_bvs))
    | None => bvs
    end) bvs anchors in
  List.iter (fun b =>
    let _ := zesu_wrap_attempt (fun () =>
      ltac1:(w0 b0 |- zesu_wrap_pose_bounds w0 b0) (Ltac1.of_constr width)
        (Ltac1.of_constr b)) in ()) bvs.

(* Reflective range first (free); else one budgeted linear call. *)
Ltac2 zesu_wrap_range (budget : zesu_wrap_budget) (width : constr) (value : constr)
    (prepare : unit -> unit) : ident :=
  let statement := constr:((0 <= $value < bv_modulus $width)%Z) in
  let name := Fresh.in_goal @HwrapRange in
  if zesu_wrap_assert name statement (fun () => ltac1:(zesu_bv_linear_range)) then name
  else if Int.le (budget.(wb_left)) 0 then Control.zero (Tactic_failure None)
  else
    (budget.(wb_left) := Int.sub (budget.(wb_left)) 1;
     if zesu_wrap_assert name statement (fun () => prepare (); ltac1:(zesu_wrap_range_solver))
     then name else Control.zero (Tactic_failure None)).

Ltac2 zesu_wrap_after (rewrite_goal : bool) (name : ident) : unit :=
  if rewrite_goal then ltac1:(h0 |- try rewrite h0) (Ltac1.of_ident name) else ().

(* One candidate: linear form, else anchored form, else (solver calls only)
   the remainder by a divisor of the modulus. *)
(* Inside a solver call (solver_mode) only the remainder by a divisor of the
   modulus is linearized: it needs no range proof. Ranges are proved at the
   cache step, once per term and block; a solver call rewrites with the
   cached equations. *)
Ltac2 zesu_wrap_has_remainder (width : constr) (term : constr) : bool :=
  let target := constr:(@bv_unsigned $width $term) in
  List.exist (fun remainder =>
    lazy_match! remainder with
    | Z.modulo ?x _ => Constr.equal x target
    | _ => false
    end) (zesu_wrap_collect constr:(Z.modulo) 8 (Control.goal ()) []).

Ltac2 zesu_wrap_one (budget : zesu_wrap_budget) (rewrite_goal : bool) (solver_mode : bool)
    (width : constr) (term : constr) : bool :=
  if Bool.and solver_mode (Bool.neg (zesu_wrap_has_remainder width term)) then false else
  match zesu_wrap_form width term with
  | None => false
  | Some f =>
      let atoms := List.append (f.(wf_bvs)) (f.(wf_zs)) in
      let read := fun () => zesu_wrap_relevant (zesu_wrap_groups budget) atoms in
      let prepare := fun () =>
        let signed := read () in
        zesu_wrap_prepare_range width (f.(wf_bvs)) signed (zesu_wrap_anchors width signed) in
      let linear := fun () => zesu_wrap_attempt (fun () =>
        let range := zesu_wrap_range budget width (f.(wf_value)) prepare in
        let name := Fresh.in_goal @HwrapLinear in
        ltac1:(n0 w0 t0 v0 r0 a0 l0 i0 c0 h0 |-
            zesu_wrap_pose_linear n0 w0 t0 v0 r0 a0 l0 i0 c0 h0)
          (Ltac1.of_ident name) (Ltac1.of_constr width) (Ltac1.of_constr term)
          (Ltac1.of_constr (f.(wf_value))) (Ltac1.of_constr (f.(wf_syntax)))
          (Ltac1.of_constr (f.(wf_atoms))) (Ltac1.of_constr (f.(wf_literals)))
          (Ltac1.of_constr (f.(wf_integers))) (Ltac1.of_constr (f.(wf_cpoly)))
          (Ltac1.of_ident range);
        zesu_wrap_after rewrite_goal name) in
      let anchored := fun () =>
        List.fold_left (fun posed anchor =>
          if posed then true
          else if Constr.equal anchor term then false
          else
            match zesu_wrap_offset width term anchor with
            | None => false
            | Some offset =>
                let value :=
                  zesu_wrap_close_sum (Some constr:(@bv_unsigned $width $anchor)) offset in
                zesu_wrap_attempt (fun () =>
                  let range := zesu_wrap_range budget width value prepare in
                  let name := Fresh.in_goal @HwrapLinear in
                  ltac1:(n0 w0 t0 b0 o0 v0 h0 |- zesu_wrap_pose_anchor n0 w0 t0 b0 o0 v0 h0)
                    (Ltac1.of_ident name) (Ltac1.of_constr width) (Ltac1.of_constr term)
                    (Ltac1.of_constr anchor) (Ltac1.of_constr offset)
                    (Ltac1.of_constr value) (Ltac1.of_ident range);
                  zesu_wrap_after rewrite_goal name)
            end) false (zesu_wrap_anchors width (read ())) in
      let modulo := fun () =>
        let target := constr:(@bv_unsigned $width $term) in
        List.fold_left (fun posed remainder =>
          if posed then true
          else
            lazy_match! remainder with
            | Z.modulo ?x ?divisor =>
                if Constr.equal x target then
                  zesu_wrap_attempt (fun () =>
                    let name := Fresh.in_goal @HwrapModulo in
                    ltac1:(n0 w0 t0 v0 r0 a0 l0 i0 c0 d0 |-
                        zesu_wrap_pose_mod n0 w0 t0 v0 r0 a0 l0 i0 c0 d0)
                      (Ltac1.of_ident name) (Ltac1.of_constr width) (Ltac1.of_constr term)
                      (Ltac1.of_constr (f.(wf_value))) (Ltac1.of_constr (f.(wf_syntax)))
                      (Ltac1.of_constr (f.(wf_atoms))) (Ltac1.of_constr (f.(wf_literals)))
                      (Ltac1.of_constr (f.(wf_integers))) (Ltac1.of_constr (f.(wf_cpoly)))
                      (Ltac1.of_constr divisor);
                    zesu_wrap_after true name)
                else false
            | _ => false
            end) false (zesu_wrap_collect constr:(Z.modulo) 8 (Control.goal ()) []) in
      if solver_mode then modulo ()
      else if linear () then true
      else anchored ()
  end.

Ltac2 zesu_wrap_refuse (terms : constr list) : unit :=
  let size := zesu_bvlin_nat (Int.add (List.length (Control.hyps ())) (List.length terms)) in
  List.iter (fun term =>
    ltac1:(t0 n0 |- pose proof (@zesu_wrap_refused_intro _ t0 n0))
      (Ltac1.of_constr term) (Ltac1.of_constr size)) terms.

(* cache: main context, honour refusals, record new ones, never rewrite.
   Solver call: rewrite the goal with posed or cached equations. *)
Ltac2 zesu_wrap_run (cache : bool) (rewrite_goal : bool)
    (candidates : (constr * constr) list) : bool :=
  let known := zesu_wrap_known cache in
  let budget := { wb_left := 8; wb_groups := None } in
  let result := List.fold_left (fun state candidate =>
    let (changed, refused) := state in
    let (width, term) := candidate in
    match List.find_opt (fun entry => let (seen, _) := entry in Constr.equal seen term) known with
    | Some entry =>
        let (_, cached) := entry in
        match cached with
        | Some name =>
            if rewrite_goal then
              let before := Control.goal () in
              ltac1:(h0 |- try rewrite h0) (Ltac1.of_ident name);
              (Bool.or changed (Bool.neg (Constr.equal before (Control.goal ()))), refused)
            else (changed, refused)
        | None => (changed, refused)
        end
    | None =>
        if zesu_wrap_one budget rewrite_goal (Bool.neg cache) width term then (true, refused)
        else (changed, term :: refused)
    end) (false, []) candidates in
  let (changed, refused) := result in
  if cache then
    match refused with
    | [] => changed
    | _ => (zesu_wrap_refuse refused; true)
    end
  else changed.

Ltac2 zesu_wrap_linearize_goal () : unit :=
  match zesu_wrap_candidates (Control.goal ()) with
  | [] => Control.zero (Tactic_failure None)
  | candidates =>
      if zesu_wrap_run false true candidates then () else Control.zero (Tactic_failure None)
  end.

Ltac2 zesu_wrap_cache_value (value : Ltac1.t) : unit :=
  match Ltac1.to_constr value with
  | Some term =>
      match zesu_wrap_candidates term with
      | [] => Control.zero (Tactic_failure None)
      | candidates =>
          if zesu_wrap_run true false candidates then () else Control.zero (Tactic_failure None)
      end
  | None => Control.zero (Tactic_failure None)
  end.

Ltac zesu_wrap_linearize := ltac2:(zesu_wrap_linearize_goal ()).

(* Solver front: fails at once unless it destructs a divisibility or poses
   or applies an equation. *)
Ltac zesu_wrap_prepare :=
  zesu_wrap_goal_head;
  progress (try zesu_wrap_divisibility; try zesu_wrap_linearize).

(* ---- Block cache step. ---- *)

Require Import isla.riscv64.riscv64.
From iris.bi Require Import interface.

Ltac zesu_wrap_cache_term term :=
  let run := ltac2:(value |- zesu_wrap_cache_value value) in
  run term.

Ltac zesu_wrap_cache_step :=
  lazymatch goal with
  | |- iris.proofmode.environments.envs_entails _ (bi_sep (bi_pure ?phi) _) =>
      zesu_wrap_cache_term phi
  | |- iris.proofmode.environments.envs_entails _ (bi_and (bi_pure ?phi) _) =>
      zesu_wrap_cache_term phi
  | |- iris.proofmode.environments.envs_entails _ (bi_wand (bi_pure ?phi) _) =>
      zesu_wrap_cache_term phi
  | |- iris.proofmode.environments.envs_entails _
        (find_in_context (FindMemMapsTo ?address) _) =>
      zesu_wrap_cache_term address
  end.
