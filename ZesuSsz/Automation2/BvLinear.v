(* A reflective linear normal form for bit-vector address arithmetic.

   A bit-vector term built from +, -, unary -, multiplication by a constant,
   shift lhs by a literal, record literals (BV n z), Z_to_bv of a linear Z
   term, and opaque atoms is reified to closed syntax: atoms are indices into
   context lists. The normalizer computes c + sum coeff_i * atom_i over Z, and
   two terms are equal (or different) as bit vectors when the difference of
   their normal forms is zero (or a non-zero constant) modulo 2^n. The checks
   run with vm_compute on the closed syntax only; the soundness lemmas below
   transfer the result to the original terms. Because the arithmetic is
   modular, an equality such as p + 16 + 8 = p + 24 or a disequality such as
   p + 8 <> p + 16 needs no range fact. *)
From Coq Require Import ZArith List Lia Bool.
From stdpp Require Import tactics bitvector.definitions.
Require Import ZesuSsz.Automation2.VmClosed.
Import ListNotations.
Local Open Scope Z_scope.

(* ---- Closed syntax. ---- *)

(* ZLUns is the unsigned value of a bit-vector atom, so that an integer
   address such as bv_unsigned x + 16 shares the key of the atom x. *)
Inductive zesuZLin : Type :=
| ZLAtom (index : nat)
| ZLUns (index : nat)
| ZLLit (value : Z)
| ZLAdd (lhs rhs : zesuZLin)
| ZLSub (lhs rhs : zesuZLin)
| ZLOpp (term : zesuZLin)
| ZLMul (lhs rhs : zesuZLin).

(* BLLit keeps the index of a record literal and its value. *)
Inductive zesuBvLin : Type :=
| BLAtom (index : nat)
| BLLit (index : nat) (value : Z)
| BLOfZ (term : zesuZLin)
| BLAdd (lhs rhs : zesuBvLin)
| BLSub (lhs rhs : zesuBvLin)
| BLOpp (term : zesuBvLin)
| BLMul (lhs rhs : zesuBvLin)
| BLShl (term amount : zesuBvLin).

(* ---- Normal form: a constant and coefficients keyed by atom kind and index. ---- *)

Definition zesuLinKey : Type := (bool * nat)%type.
Definition zesuLinPoly : Type := (Z * list (zesuLinKey * Z))%type.

Definition zesuKeyEqb (lhs rhs : zesuLinKey) : bool :=
  Bool.eqb (fst lhs) (fst rhs) && Nat.eqb (snd lhs) (snd rhs).

Fixpoint zesuTermsInsert (key : zesuLinKey) (coeff : Z) (terms : list (zesuLinKey * Z))
    : list (zesuLinKey * Z) :=
  match terms with
  | [] => [(key, coeff)]
  | (other, value) :: rest =>
      if zesuKeyEqb key other then (other, value + coeff) :: rest
      else (other, value) :: zesuTermsInsert key coeff rest
  end.

Fixpoint zesuTermsAdd (lhs rhs : list (zesuLinKey * Z)) : list (zesuLinKey * Z) :=
  match lhs with
  | [] => rhs
  | (key, coeff) :: rest => zesuTermsInsert key coeff (zesuTermsAdd rest rhs)
  end.

Definition zesuTermsScale (factor : Z) (terms : list (zesuLinKey * Z)) : list (zesuLinKey * Z) :=
  map (fun entry => (fst entry, factor * snd entry)) terms.

Definition zesuPolyAdd (lhs rhs : zesuLinPoly) : zesuLinPoly :=
  (fst lhs + fst rhs, zesuTermsAdd (snd lhs) (snd rhs)).
Definition zesuPolyScale (factor : Z) (poly : zesuLinPoly) : zesuLinPoly :=
  (factor * fst poly, zesuTermsScale factor (snd poly)).
Definition zesuPolyNeg (poly : zesuLinPoly) : zesuLinPoly := zesuPolyScale (-1) poly.
Definition zesuPolyConst (poly : zesuLinPoly) : option Z :=
  match snd poly with [] => Some (fst poly) | _ => None end.

Definition zesuPolyMul (lhs rhs : zesuLinPoly) : option zesuLinPoly :=
  match zesuPolyConst lhs, zesuPolyConst rhs with
  | Some factor, _ => Some (zesuPolyScale factor rhs)
  | None, Some factor => Some (zesuPolyScale factor lhs)
  | None, None => None
  end.

Fixpoint zesuZNorm (term : zesuZLin) : option zesuLinPoly :=
  match term with
  | ZLAtom index => Some (0, [((false, index), 1)])
  | ZLUns index => Some (0, [((true, index), 1)])
  | ZLLit value => Some (value, [])
  | ZLAdd lhs rhs =>
      match zesuZNorm lhs, zesuZNorm rhs with
      | Some p, Some q => Some (zesuPolyAdd p q) | _, _ => None end
  | ZLSub lhs rhs =>
      match zesuZNorm lhs, zesuZNorm rhs with
      | Some p, Some q => Some (zesuPolyAdd p (zesuPolyNeg q)) | _, _ => None end
  | ZLOpp inner =>
      match zesuZNorm inner with Some p => Some (zesuPolyNeg p) | None => None end
  | ZLMul lhs rhs =>
      match zesuZNorm lhs, zesuZNorm rhs with
      | Some p, Some q => zesuPolyMul p q | _, _ => None end
  end.

(* A lhs shift by k multiplies by 2^k; a shift by at least the width gives 0. *)
Definition zesuShiftPoly (width : N) (amount : zesuLinPoly) (poly : zesuLinPoly)
    : option zesuLinPoly :=
  match zesuPolyConst amount with
  | Some value =>
      let shift := value mod bv_modulus width in
      if shift <? Z.of_N width then Some (zesuPolyScale (2 ^ shift) poly)
      else Some (0, [])
  | None => None
  end.

Fixpoint zesuBvNorm (width : N) (term : zesuBvLin) : option zesuLinPoly :=
  match term with
  | BLAtom index => Some (0, [((true, index), 1)])
  | BLLit _ value => Some (value, [])
  | BLOfZ inner => zesuZNorm inner
  | BLAdd lhs rhs =>
      match zesuBvNorm width lhs, zesuBvNorm width rhs with
      | Some p, Some q => Some (zesuPolyAdd p q) | _, _ => None end
  | BLSub lhs rhs =>
      match zesuBvNorm width lhs, zesuBvNorm width rhs with
      | Some p, Some q => Some (zesuPolyAdd p (zesuPolyNeg q)) | _, _ => None end
  | BLOpp inner =>
      match zesuBvNorm width inner with Some p => Some (zesuPolyNeg p) | None => None end
  | BLMul lhs rhs =>
      match zesuBvNorm width lhs, zesuBvNorm width rhs with
      | Some p, Some q => zesuPolyMul p q | _, _ => None end
  | BLShl inner amount =>
      match zesuBvNorm width amount, zesuBvNorm width inner with
      | Some a, Some p => zesuShiftPoly width a p | _, _ => None end
  end.

Definition zesuTermsZeroMod (modulus : Z) (terms : list (zesuLinKey * Z)) : bool :=
  forallb (fun entry => Z.eqb (snd entry mod modulus) 0) terms.

Definition zesuBvLinEqCheck (width : N) (lhs rhs : zesuBvLin) : bool :=
  match zesuBvNorm width lhs, zesuBvNorm width rhs with
  | Some p, Some q =>
      let difference := zesuPolyAdd p (zesuPolyNeg q) in
      Z.eqb (fst difference mod bv_modulus width) 0 &&
      zesuTermsZeroMod (bv_modulus width) (snd difference)
  | _, _ => false
  end.

Definition zesuBvLinNeCheck (width : N) (lhs rhs : zesuBvLin) : bool :=
  match zesuBvNorm width lhs, zesuBvNorm width rhs with
  | Some p, Some q =>
      let difference := zesuPolyAdd p (zesuPolyNeg q) in
      negb (Z.eqb (fst difference mod bv_modulus width) 0) &&
      zesuTermsZeroMod (bv_modulus width) (snd difference)
  | _, _ => false
  end.

(* Every record literal of the term has the value that its syntax records. *)
Fixpoint zesuBvLinLitCheck {width : N} (literals : list (bv width)) (term : zesuBvLin) : bool :=
  match term with
  | BLAtom _ | BLOfZ _ => true
  | BLLit index value => Z.eqb (bv_unsigned (nth index literals (Z_to_bv width 0))) value
  | BLAdd lhs rhs | BLSub lhs rhs | BLMul lhs rhs =>
      zesuBvLinLitCheck literals lhs && zesuBvLinLitCheck literals rhs
  | BLOpp inner => zesuBvLinLitCheck literals inner
  | BLShl inner amount => zesuBvLinLitCheck literals inner && zesuBvLinLitCheck literals amount
  end.

(* ---- Denotation and soundness. ---- *)

(* Bounds of a linear integer term whose atoms are all unsigned values of
   bit vectors (each in [0, top]); None when an integer atom occurs. *)
Fixpoint zesuTermsBounds (top : Z) (terms : list (zesuLinKey * Z)) : option (Z * Z) :=
  match terms with
  | [] => Some (0, 0)
  | ((true, _), coeff) :: rest =>
      match zesuTermsBounds top rest with
      | Some (low, high) => Some (Z.min 0 (coeff * top) + low, Z.max 0 (coeff * top) + high)
      | None => None
      end
  | ((false, _), _) :: _ => None
  end.

Definition zesuRangeCheck (width : N) (term : zesuZLin) : bool :=
  match zesuZNorm term with
  | Some (constant, terms) =>
      match zesuTermsBounds (bv_modulus width - 1) terms with
      | Some (low, high) => (0 <=? constant + low) && (constant + high <? bv_modulus width)
      | None => false
      end
  | None => false
  end.

Section denote.
Context {width : N} (atoms literals : list (bv width)) (integers : list Z).

Fixpoint zesuZLinDenote (term : zesuZLin) : Z :=
  match term with
  | ZLAtom index => nth index integers 0
  | ZLUns index => bv_unsigned (nth index atoms (Z_to_bv width 0))
  | ZLLit value => value
  | ZLAdd lhs rhs => zesuZLinDenote lhs + zesuZLinDenote rhs
  | ZLSub lhs rhs => zesuZLinDenote lhs - zesuZLinDenote rhs
  | ZLOpp inner => - zesuZLinDenote inner
  | ZLMul lhs rhs => zesuZLinDenote lhs * zesuZLinDenote rhs
  end.

Fixpoint zesuBvLinDenote (term : zesuBvLin) : bv width :=
  match term with
  | BLAtom index => nth index atoms (Z_to_bv width 0)
  | BLLit index _ => nth index literals (Z_to_bv width 0)
  | BLOfZ inner => Z_to_bv width (zesuZLinDenote inner)
  | BLAdd lhs rhs => bv_add (zesuBvLinDenote lhs) (zesuBvLinDenote rhs)
  | BLSub lhs rhs => bv_sub (zesuBvLinDenote lhs) (zesuBvLinDenote rhs)
  | BLOpp inner => bv_opp (zesuBvLinDenote inner)
  | BLMul lhs rhs => bv_mul (zesuBvLinDenote lhs) (zesuBvLinDenote rhs)
  | BLShl inner amount => bv_shiftl (zesuBvLinDenote inner) (zesuBvLinDenote amount)
  end.

Definition zesuKeyValue (key : zesuLinKey) : Z :=
  if fst key then bv_unsigned (nth (snd key) atoms (Z_to_bv width 0))
  else nth (snd key) integers 0.

Fixpoint zesuTermsEval (terms : list (zesuLinKey * Z)) : Z :=
  match terms with
  | [] => 0
  | (key, coeff) :: rest => coeff * zesuKeyValue key + zesuTermsEval rest
  end.

Definition zesuPolyEval (poly : zesuLinPoly) : Z := fst poly + zesuTermsEval (snd poly).

Lemma zesuKeyEqb_eq lhs rhs : zesuKeyEqb lhs rhs = true -> lhs = rhs.
Proof.
  destruct lhs as [b i], rhs as [c j]. unfold zesuKeyEqb. cbn.
  intros [Hb Hi]%andb_true_iff. apply Bool.eqb_prop in Hb. apply Nat.eqb_eq in Hi. congruence.
Qed.

Lemma zesuTermsInsert_eval key coeff terms :
  zesuTermsEval (zesuTermsInsert key coeff terms) = coeff * zesuKeyValue key + zesuTermsEval terms.
Proof.
  induction terms as [|[other value] rest IH]; cbn; [lia|].
  destruct (zesuKeyEqb key other) eqn:Hkey.
  - apply zesuKeyEqb_eq in Hkey. subst other. cbn. ring.
  - cbn. rewrite IH. ring.
Qed.

Lemma zesuTermsAdd_eval lhs rhs :
  zesuTermsEval (zesuTermsAdd lhs rhs) = zesuTermsEval lhs + zesuTermsEval rhs.
Proof.
  induction lhs as [|[key coeff] rest IH]; cbn; [lia|].
  rewrite zesuTermsInsert_eval, IH. ring.
Qed.

Lemma zesuTermsScale_eval factor terms :
  zesuTermsEval (zesuTermsScale factor terms) = factor * zesuTermsEval terms.
Proof.
  unfold zesuTermsScale. induction terms as [|[key coeff] rest IH]; cbn; [lia|].
  rewrite IH. ring.
Qed.

Lemma zesuPolyAdd_eval p q : zesuPolyEval (zesuPolyAdd p q) = zesuPolyEval p + zesuPolyEval q.
Proof. unfold zesuPolyEval, zesuPolyAdd. cbn [fst snd]. rewrite zesuTermsAdd_eval. ring. Qed.

Lemma zesuPolyScale_eval factor p :
  zesuPolyEval (zesuPolyScale factor p) = factor * zesuPolyEval p.
Proof. unfold zesuPolyEval, zesuPolyScale. cbn [fst snd]. rewrite zesuTermsScale_eval. ring. Qed.

Lemma zesuPolyNeg_eval p : zesuPolyEval (zesuPolyNeg p) = - zesuPolyEval p.
Proof. unfold zesuPolyNeg. rewrite zesuPolyScale_eval. ring. Qed.

Lemma zesuPolyConst_eval p value : zesuPolyConst p = Some value -> zesuPolyEval p = value.
Proof.
  destruct p as [c terms]. unfold zesuPolyConst, zesuPolyEval. cbn.
  destruct terms; intros Heq; inversion Heq; cbn; lia.
Qed.

Lemma zesuPolyMul_eval p q r :
  zesuPolyMul p q = Some r -> zesuPolyEval r = zesuPolyEval p * zesuPolyEval q.
Proof.
  unfold zesuPolyMul.
  destruct (zesuPolyConst p) as [factor|] eqn:Hp.
  - intros Heq. inversion Heq; subst. rewrite zesuPolyScale_eval.
    rewrite (zesuPolyConst_eval _ _ Hp). reflexivity.
  - destruct (zesuPolyConst q) as [factor|] eqn:Hq; [|discriminate].
    intros Heq. inversion Heq; subst. rewrite zesuPolyScale_eval.
    rewrite (zesuPolyConst_eval _ _ Hq). ring.
Qed.

Lemma zesuZNorm_sound term poly :
  zesuZNorm term = Some poly -> zesuPolyEval poly = zesuZLinDenote term.
Proof.
  revert poly. induction term as [index|index|value|l IHl r IHr|l IHl r IHr|t IHt|l IHl r IHr];
    intros poly Hnorm; cbn in Hnorm |- *.
  - inversion Hnorm. unfold zesuPolyEval, zesuKeyValue. cbn. ring.
  - inversion Hnorm. unfold zesuPolyEval, zesuKeyValue. cbn. ring.
  - inversion Hnorm. unfold zesuPolyEval. cbn. ring.
  - destruct (zesuZNorm l) as [pl|] eqn:Hl, (zesuZNorm r) as [pr|] eqn:Hr; try discriminate.
    inversion Hnorm. rewrite zesuPolyAdd_eval, (IHl _ eq_refl), (IHr _ eq_refl). reflexivity.
  - destruct (zesuZNorm l) as [pl|] eqn:Hl, (zesuZNorm r) as [pr|] eqn:Hr; try discriminate.
    inversion Hnorm. rewrite zesuPolyAdd_eval, zesuPolyNeg_eval, (IHl _ eq_refl), (IHr _ eq_refl). ring.
  - destruct (zesuZNorm t) as [pt|] eqn:Ht; try discriminate.
    inversion Hnorm. rewrite zesuPolyNeg_eval, (IHt _ eq_refl). reflexivity.
  - destruct (zesuZNorm l) as [pl|] eqn:Hl, (zesuZNorm r) as [pr|] eqn:Hr; try discriminate.
    rewrite (zesuPolyMul_eval _ _ _ Hnorm), (IHl _ eq_refl), (IHr _ eq_refl). reflexivity.
Qed.

Lemma zesu_bv_wrap_mod z : bv_wrap width z = z mod bv_modulus width.
Proof. reflexivity. Qed.

Lemma zesu_bv_modulus_pos : 0 < bv_modulus width.
Proof. apply bv_modulus_pos. Qed.

Lemma zesuBvNorm_sound term poly :
  zesuBvLinLitCheck literals term = true ->
  zesuBvNorm width term = Some poly ->
  bv_unsigned (zesuBvLinDenote term) = bv_wrap width (zesuPolyEval poly).
Proof.
  pose proof zesu_bv_modulus_pos as Hpos.
  revert poly.
  induction term as [index|index value|inner|l IHl r IHr|l IHl r IHr|t IHt|l IHl r IHr|t IHt a IHa];
    intros poly Hlit Hnorm; cbn in Hlit, Hnorm |- *.
  - inversion Hnorm; subst. unfold zesuPolyEval, zesuKeyValue. cbn.
    rewrite ?Z.mul_1_l, ?Z.add_0_l, ?Z.add_0_r.
    symmetry. apply bv_wrap_small. apply bv_unsigned_in_range.
  - inversion Hnorm; subst. apply Z.eqb_eq in Hlit. unfold zesuPolyEval. cbn.
    rewrite ?Z.add_0_r, <- Hlit. symmetry. apply bv_wrap_small. apply bv_unsigned_in_range.
  - rewrite Z_to_bv_unsigned. f_equal. symmetry. apply zesuZNorm_sound. exact Hnorm.
  - apply andb_true_iff in Hlit as [Hll Hlr].
    destruct (zesuBvNorm width l) as [pl|] eqn:Hl, (zesuBvNorm width r) as [pr|] eqn:Hr;
      try discriminate.
    inversion Hnorm; subst. rewrite bv_add_unsigned, (IHl _ Hll eq_refl), (IHr _ Hlr eq_refl).
    rewrite zesuPolyAdd_eval, !zesu_bv_wrap_mod, Zplus_mod_idemp_l, Zplus_mod_idemp_r. reflexivity.
  - apply andb_true_iff in Hlit as [Hll Hlr].
    destruct (zesuBvNorm width l) as [pl|] eqn:Hl, (zesuBvNorm width r) as [pr|] eqn:Hr;
      try discriminate.
    inversion Hnorm; subst. rewrite bv_sub_unsigned, (IHl _ Hll eq_refl), (IHr _ Hlr eq_refl).
    rewrite zesuPolyAdd_eval, zesuPolyNeg_eval, !zesu_bv_wrap_mod.
    rewrite Zminus_mod_idemp_l, Zminus_mod_idemp_r. f_equal; try ring.
  - destruct (zesuBvNorm width t) as [pt|] eqn:Ht; try discriminate.
    inversion Hnorm; subst. rewrite bv_opp_unsigned, (IHt _ Hlit eq_refl).
    rewrite zesuPolyNeg_eval, !zesu_bv_wrap_mod.
    rewrite <- (Z.sub_0_l (zesuPolyEval pt mod bv_modulus width)), <- (Z.sub_0_l (zesuPolyEval pt)).
    apply Zminus_mod_idemp_r.
  - apply andb_true_iff in Hlit as [Hll Hlr].
    destruct (zesuBvNorm width l) as [pl|] eqn:Hl, (zesuBvNorm width r) as [pr|] eqn:Hr;
      try discriminate.
    rewrite bv_mul_unsigned, (IHl _ Hll eq_refl), (IHr _ Hlr eq_refl).
    rewrite (zesuPolyMul_eval _ _ _ Hnorm), !zesu_bv_wrap_mod.
    rewrite Zmult_mod_idemp_l, Zmult_mod_idemp_r. reflexivity.
  - apply andb_true_iff in Hlit as [Hlt Hla].
    destruct (zesuBvNorm width a) as [pa|] eqn:Ha, (zesuBvNorm width t) as [pt|] eqn:Ht;
      try discriminate.
    unfold zesuShiftPoly in Hnorm.
    destruct (zesuPolyConst pa) as [value|] eqn:Hconst; [|discriminate].
    rewrite bv_shiftl_unsigned, (IHt _ Hlt eq_refl), (IHa _ Hla eq_refl).
    rewrite (zesuPolyConst_eval _ _ Hconst), !zesu_bv_wrap_mod.
    assert (Hshift : 0 <= value mod bv_modulus width) by (apply Z.mod_pos_bound; lia).
    rewrite Z.shiftl_mul_pow2 by exact Hshift.
    destruct (value mod bv_modulus width <? Z.of_N width) eqn:Hsmall.
    + inversion Hnorm; subst. rewrite zesuPolyScale_eval.
      rewrite Zmult_mod_idemp_l. f_equal; try ring.
    + inversion Hnorm; subst. apply Z.ltb_ge in Hsmall.
      assert (Hpow : 2 ^ (value mod bv_modulus width) =
        bv_modulus width * 2 ^ (value mod bv_modulus width - Z.of_N width)).
      { unfold bv_modulus at 2. rewrite <- Z.pow_add_r by lia. f_equal. ring. }
      rewrite Hpow.
      replace (zesuPolyEval pt mod bv_modulus width *
        (bv_modulus width * 2 ^ (value mod bv_modulus width - Z.of_N width))) with
        (zesuPolyEval pt mod bv_modulus width *
          2 ^ (value mod bv_modulus width - Z.of_N width) * bv_modulus width) by ring.
      rewrite Z_mod_mult. reflexivity.
Qed.

Lemma zesuTermsZeroMod_eval modulus terms :
  0 < modulus -> zesuTermsZeroMod modulus terms = true -> zesuTermsEval terms mod modulus = 0.
Proof.
  intros Hpos. induction terms as [|[key coeff] rest IH]; cbn; [reflexivity|].
  intros [Hcoeff Hrest]%andb_true_iff. apply Z.eqb_eq in Hcoeff.
  rewrite Z.add_mod, Z.mul_mod, Hcoeff, (IH Hrest) by lia. reflexivity.
Qed.

Lemma zesu_mod_eq_of_sub_mod x y modulus :
  0 < modulus -> (x - y) mod modulus = 0 -> x mod modulus = y mod modulus.
Proof.
  intros Hpos Hzero.
  assert (Hdiv : (modulus | x - y)) by (apply Z.mod_divide; [lia | exact Hzero]).
  destruct Hdiv as [k Hk]. replace x with (y + k * modulus) by lia. apply Z.mod_add. lia.
Qed.

Theorem zesuBvLinEq_sound lhs rhs :
  zesuBvLinLitCheck literals lhs && zesuBvLinLitCheck literals rhs = true ->
  zesuBvLinEqCheck width lhs rhs = true ->
  zesuBvLinDenote lhs = zesuBvLinDenote rhs.
Proof.
  intros [Hlitl Hlitr]%andb_true_iff Hcheck.
  pose proof zesu_bv_modulus_pos as Hpos.
  unfold zesuBvLinEqCheck in Hcheck. cbv zeta in Hcheck.
  destruct (zesuBvNorm width lhs) as [p|] eqn:Hl, (zesuBvNorm width rhs) as [q|] eqn:Hr;
    try discriminate.
  apply andb_true_iff in Hcheck as [Hconst Hterms]. apply Z.eqb_eq in Hconst.
  apply bv_eq. rewrite (zesuBvNorm_sound _ _ Hlitl Hl), (zesuBvNorm_sound _ _ Hlitr Hr).
  rewrite !zesu_bv_wrap_mod. apply zesu_mod_eq_of_sub_mod; [exact Hpos|].
  pose proof (zesuTermsZeroMod_eval _ _ Hpos Hterms) as Hzero.
  replace (zesuPolyEval p - zesuPolyEval q) with (zesuPolyEval (zesuPolyAdd p (zesuPolyNeg q)))
    by (rewrite zesuPolyAdd_eval, zesuPolyNeg_eval; ring).
  unfold zesuPolyEval at 1. rewrite Z.add_mod, Hconst, Hzero by lia. reflexivity.
Qed.

Theorem zesuBvLinNe_sound lhs rhs :
  zesuBvLinLitCheck literals lhs && zesuBvLinLitCheck literals rhs = true ->
  zesuBvLinNeCheck width lhs rhs = true ->
  zesuBvLinDenote lhs <> zesuBvLinDenote rhs.
Proof.
  intros [Hlitl Hlitr]%andb_true_iff Hcheck Heq.
  pose proof zesu_bv_modulus_pos as Hpos.
  unfold zesuBvLinNeCheck in Hcheck. cbv zeta in Hcheck.
  destruct (zesuBvNorm width lhs) as [p|] eqn:Hl, (zesuBvNorm width rhs) as [q|] eqn:Hr;
    try discriminate.
  apply andb_true_iff in Hcheck as [Hconst Hterms]. apply negb_true_iff, Z.eqb_neq in Hconst.
  apply (f_equal bv_unsigned) in Heq.
  rewrite (zesuBvNorm_sound _ _ Hlitl Hl), (zesuBvNorm_sound _ _ Hlitr Hr), !zesu_bv_wrap_mod in Heq.
  apply Hconst.
  pose proof (zesuTermsZeroMod_eval _ _ Hpos Hterms) as Hzero.
  assert (Hdiff : (zesuPolyEval p - zesuPolyEval q) mod bv_modulus width = 0).
  { rewrite Zminus_mod, Heq, Z.sub_diag. reflexivity. }
  replace (zesuPolyEval p - zesuPolyEval q) with (zesuPolyEval (zesuPolyAdd p (zesuPolyNeg q)))
    in Hdiff by (rewrite zesuPolyAdd_eval, zesuPolyNeg_eval; ring).
  unfold zesuPolyEval in Hdiff. rewrite Z.add_mod, Hzero, Z.add_0_r, Z.mod_mod in Hdiff by lia.
  exact Hdiff.
Qed.
Lemma zesuTermsBounds_sound terms low high :
  zesuTermsBounds (bv_modulus width - 1) terms = Some (low, high) ->
  low <= zesuTermsEval terms <= high.
Proof.
  revert low high.
  induction terms as [|[[kind index] coeff] rest IH]; intros low high Hbounds; cbn in Hbounds |- *.
  - inversion Hbounds; subst. lia.
  - destruct kind; [|discriminate].
    destruct (zesuTermsBounds (bv_modulus width - 1) rest) as [[l h]|] eqn:Hrest; [|discriminate].
    inversion Hbounds; subst. specialize (IH l h eq_refl).
    unfold zesuKeyValue. cbn [fst snd].
    pose proof (bv_unsigned_in_range _ (nth index atoms (Z_to_bv width 0))) as Hin.
    destruct (Z.le_ge_cases 0 coeff) as [Hc|Hc].
    + rewrite Z.min_l, Z.max_r by nia. nia.
    + rewrite Z.min_r, Z.max_l by nia. nia.
Qed.

Theorem zesuRange_sound term :
  zesuRangeCheck width term = true -> 0 <= zesuZLinDenote term < bv_modulus width.
Proof.
  unfold zesuRangeCheck. intros Hcheck.
  destruct (zesuZNorm term) as [[constant terms]|] eqn:Hnorm; [|discriminate].
  destruct (zesuTermsBounds (bv_modulus width - 1) terms) as [[low high]|] eqn:Hbounds;
    [|discriminate].
  apply andb_true_iff in Hcheck as [Hlow Hhigh].
  apply Z.leb_le in Hlow. apply Z.ltb_lt in Hhigh.
  rewrite <- (zesuZNorm_sound _ _ Hnorm). unfold zesuPolyEval. cbn [fst snd].
  pose proof (zesuTermsBounds_sound _ _ _ Hbounds). lia.
Qed.

End denote.

(* ---- Integer goals that map back to bit vectors. ---- *)

Lemma zesu_bv_unsigned_eq_of_eq {width : N} (lhs rhs : bv width) :
  lhs = rhs -> bv_unsigned lhs = bv_unsigned rhs.
Proof. intros ->. reflexivity. Qed.

Lemma zesu_bv_unsigned_ne_of_ne {width : N} (lhs rhs : bv width) :
  lhs <> rhs -> bv_unsigned lhs <> bv_unsigned rhs.
Proof. intros Hne Heq. apply Hne, bv_eq, Heq. Qed.

Lemma zesu_bv_unsigned_eq_of_cast {width : N} (term : bv width) (value : Z) :
  term = Z_to_bv width value -> 0 <= value < bv_modulus width -> bv_unsigned term = value.
Proof. intros -> Hrange. apply Z_to_bv_small. exact Hrange. Qed.

Lemma zesu_bv_unsigned_ne_of_cast {width : N} (term : bv width) (value : Z) :
  term <> Z_to_bv width value -> bv_unsigned term <> value.
Proof.
  intros Hne Heq. apply Hne. apply bv_eq. rewrite Z_to_bv_unsigned, <- Heq.
  symmetry. apply bv_wrap_small. apply bv_unsigned_in_range.
Qed.

(* ---- Reification in Ltac2. ---- *)

From Ltac2 Require Import Ltac2 Constr Std.
Set Default Proof Mode "Classic".

Ltac2 Type zesu_bvlin_state := {
  mutable bv_atoms : constr list;
  mutable bv_literals : constr list;
  mutable z_atoms : constr list }.

Ltac2 rec zesu_bvlin_index (term : constr) (terms : constr list) (position : int) : int option :=
  match terms with
  | [] => None
  | head :: rest =>
      if Constr.equal term head then Some position
      else zesu_bvlin_index term rest (Int.add position 1)
  end.

Ltac2 rec zesu_bvlin_nat (value : int) : constr :=
  if Int.equal value 0 then constr:(O)
  else let inner := zesu_bvlin_nat (Int.sub value 1) in constr:(S $inner).

(* Index of term in the list, appending it when it is new. *)
Ltac2 zesu_bvlin_lookup (terms : constr list) (term : constr) : int * constr list :=
  match zesu_bvlin_index term terms 0 with
  | Some position => (position, terms)
  | None => (List.length terms, List.append terms [term])
  end.

Ltac2 zesu_bvlin_closed (term : constr) : bool :=
  Control.plus (fun () => ltac1:(term |- ZesuSsz.Automation2.VmClosed.zesu_vm_closed term) (Ltac1.of_constr term); true)
    (fun _ => false).

Ltac2 zesu_bvlin_bv_atom (state : zesu_bvlin_state) (term : constr) : constr :=
  let (position, atoms) := zesu_bvlin_lookup (state.(bv_atoms)) term in
  state.(bv_atoms) := atoms;
  zesu_bvlin_nat position.

Ltac2 rec zesu_bvlin_reify_z (width : constr) (state : zesu_bvlin_state) (term : constr) : constr :=
  lazy_match! term with
  | Z.add ?lhs ?rhs =>
      let l := zesu_bvlin_reify_z width state lhs in let r := zesu_bvlin_reify_z width state rhs in
      constr:(ZLAdd $l $r)
  | Z.sub ?lhs ?rhs =>
      let l := zesu_bvlin_reify_z width state lhs in let r := zesu_bvlin_reify_z width state rhs in
      constr:(ZLSub $l $r)
  | Z.opp ?inner => let i := zesu_bvlin_reify_z width state inner in constr:(ZLOpp $i)
  | Z.mul ?lhs ?rhs =>
      if Bool.or (zesu_bvlin_closed lhs) (zesu_bvlin_closed rhs) then
        let l := zesu_bvlin_reify_z width state lhs in let r := zesu_bvlin_reify_z width state rhs in
        constr:(ZLMul $l $r)
      else
        let (position, atoms) := zesu_bvlin_lookup (state.(z_atoms)) term in
        state.(z_atoms) := atoms;
        let index := zesu_bvlin_nat position in constr:(ZLAtom $index)
  | @bv_unsigned ?w ?inner =>
      if Constr.equal w width then
        let index := zesu_bvlin_bv_atom state inner in constr:(ZLUns $index)
      else
        let (position, atoms) := zesu_bvlin_lookup (state.(z_atoms)) term in
        state.(z_atoms) := atoms;
        let index := zesu_bvlin_nat position in constr:(ZLAtom $index)
  | _ =>
      if zesu_bvlin_closed term then constr:(ZLLit $term)
      else
        let (position, atoms) := zesu_bvlin_lookup (state.(z_atoms)) term in
        state.(z_atoms) := atoms;
        let index := zesu_bvlin_nat position in constr:(ZLAtom $index)
  end.

Ltac2 rec zesu_bvlin_reify (width : constr) (state : zesu_bvlin_state) (term : constr) : constr :=
  lazy_match! term with
  | bv_add ?lhs ?rhs =>
      let l := zesu_bvlin_reify width state lhs in let r := zesu_bvlin_reify width state rhs in
      constr:(BLAdd $l $r)
  | bv_sub ?lhs ?rhs =>
      let l := zesu_bvlin_reify width state lhs in let r := zesu_bvlin_reify width state rhs in
      constr:(BLSub $l $r)
  | bv_opp ?inner => let i := zesu_bvlin_reify width state inner in constr:(BLOpp $i)
  | bv_mul ?lhs ?rhs =>
      if Bool.or (zesu_bvlin_closed lhs) (zesu_bvlin_closed rhs) then
        let l := zesu_bvlin_reify width state lhs in let r := zesu_bvlin_reify width state rhs in
        constr:(BLMul $l $r)
      else let index := zesu_bvlin_bv_atom state term in constr:(BLAtom $index)
  | bv_shiftl ?inner ?amount =>
      if zesu_bvlin_closed amount then
        let i := zesu_bvlin_reify width state inner in let a := zesu_bvlin_reify width state amount in
        constr:(BLShl $i $a)
      else let index := zesu_bvlin_bv_atom state term in constr:(BLAtom $index)
  | Z_to_bv _ ?value => let v := zesu_bvlin_reify_z width state value in constr:(BLOfZ $v)
  | @BV _ ?value _ =>
      if zesu_bvlin_closed term then
        let (position, literals) := zesu_bvlin_lookup (state.(bv_literals)) term in
        state.(bv_literals) := literals;
        let index := zesu_bvlin_nat position in constr:(BLLit $index $value)
      else
        let (position, atoms) := zesu_bvlin_lookup (state.(bv_atoms)) term in
        state.(bv_atoms) := atoms;
        let index := zesu_bvlin_nat position in constr:(BLAtom $index)
  | _ =>
      let (position, atoms) := zesu_bvlin_lookup (state.(bv_atoms)) term in
      state.(bv_atoms) := atoms;
      let index := zesu_bvlin_nat position in constr:(BLAtom $index)
  end.

Ltac2 rec zesu_bvlin_list (kind : constr) (terms : constr list) : constr :=
  match terms with
  | [] => constr:(@nil $kind)
  | head :: rest => let tail := zesu_bvlin_list kind rest in constr:(@cons $kind $head $tail)
  end.

Ltac2 zesu_bvlin_close_check () :=
  ltac1:(ZesuSsz.Automation2.VmClosed.zesu_vm_compute_closed; reflexivity).

(* Prove lhs = rhs (eq) or lhs <> rhs (ne) for bit vectors of width width. *)
Ltac2 zesu_bvlin_prove (width : constr) (lhs : constr) (rhs : constr) (equal : bool) :=
  let state := { bv_atoms := []; bv_literals := []; z_atoms := [] } in
  let l := zesu_bvlin_reify width state lhs in
  let r := zesu_bvlin_reify width state rhs in
  let kind := constr:(bv $width) in
  let atoms := zesu_bvlin_list kind (state.(bv_atoms)) in
  let literals := zesu_bvlin_list kind (state.(bv_literals)) in
  let integers := zesu_bvlin_list constr:(Z) (state.(z_atoms)) in
  (if equal then
     refine '(@zesuBvLinEq_sound $width $atoms $literals $integers $l $r _ _)
   else
     refine '(@zesuBvLinNe_sound $width $atoms $literals $integers $l $r _ _));
  Control.enter zesu_bvlin_close_check.

Ltac2 zesu_bvlin_goal () :=
  lazy_match! goal with
  | [ |- @eq (bv ?width) ?lhs ?rhs ] => zesu_bvlin_prove width lhs rhs true
  | [ |- not (@eq (bv ?width) ?lhs ?rhs) ] => zesu_bvlin_prove width lhs rhs false
  | [ |- @eq (bv ?width) ?lhs ?rhs -> False ] => zesu_bvlin_prove width lhs rhs false
  end.

Ltac zesu_bv_linear_bv := ltac2:(zesu_bvlin_goal ()).

(* Prove 0 <= value < bv_modulus width when value is linear in unsigned
   values of bit vectors only. *)
Ltac2 zesu_bvlin_range_goal () :=
  lazy_match! goal with
  | [ |- Z.le 0 ?value /\ Z.lt ?value (bv_modulus ?width) ] =>
      let state := { bv_atoms := []; bv_literals := []; z_atoms := [] } in
      let v := zesu_bvlin_reify_z width state value in
      let kind := constr:(bv $width) in
      let atoms := zesu_bvlin_list kind (state.(bv_atoms)) in
      let integers := zesu_bvlin_list constr:(Z) (state.(z_atoms)) in
      refine '(@zesuRange_sound $width $atoms $integers $v _);
      Control.enter zesu_bvlin_close_check
  end.

Ltac zesu_bv_linear_range := ltac2:(zesu_bvlin_range_goal ()).

(* The modulus of a literal width is a closed term. The range solver gets
   its value as an equation, so that facts stated with bv_modulus and facts
   stated with a numeral both apply. *)
Ltac zesu_bv_modulus_value :=
  repeat match goal with
  | |- context [bv_modulus ?width] =>
      lazymatch goal with
      | _ : bv_modulus width = _ |- _ => fail
      | _ =>
          let value := ZesuSsz.Automation2.VmClosed.zesu_vm_eval_closed (bv_modulus width) in
          pose proof (eq_refl : bv_modulus width = value)
      end
  end.

(* The range of a cast: by bounds of unsigned values first, else by the
   given solver. *)
Ltac zesu_bv_linear_cast_range range :=
  first [zesu_bv_linear_range | zesu_bv_modulus_value; range].

(* The fast path: bit-vector (in)equalities, and integer (in)equalities of
   unsigned values that map back soundly. The integer cast form leaves only
   its range to the given solver. Any other goal, and a goal with an evar,
   fails at once. *)
Ltac zesu_bv_linear_with range :=
  lazymatch goal with |- ?goal => tryif has_evar goal then fail 0 else idtac end;
  lazymatch goal with
  | |- @eq (bv _) _ _ => solve [zesu_bv_linear_bv]
  | |- not (@eq (bv _) _ _) => solve [zesu_bv_linear_bv]
  | |- @eq Z (bv_unsigned ?lhs) (bv_unsigned ?rhs) =>
      solve [apply (zesu_bv_unsigned_eq_of_eq lhs rhs); zesu_bv_linear_bv]
  | |- not (@eq Z (bv_unsigned ?lhs) (bv_unsigned ?rhs)) =>
      solve [apply (zesu_bv_unsigned_ne_of_ne lhs rhs); zesu_bv_linear_bv]
  | |- @eq Z (@bv_unsigned ?width ?term) ?value =>
      solve [apply (zesu_bv_unsigned_eq_of_cast (width := width) term value);
        [zesu_bv_linear_bv | zesu_bv_linear_cast_range range]]
  | |- @eq Z ?value (@bv_unsigned ?width ?term) =>
      solve [symmetry; apply (zesu_bv_unsigned_eq_of_cast (width := width) term value);
        [zesu_bv_linear_bv | zesu_bv_linear_cast_range range]]
  | |- not (@eq Z (@bv_unsigned ?width ?term) ?value) =>
      solve [apply (zesu_bv_unsigned_ne_of_cast (width := width) term value); zesu_bv_linear_bv]
  end.

(* Succeed, goal unchanged, when the normal form proves the goal equality false
   for every value of its atoms (the sides differ by a non-zero constant modulo
   2^width). Hypotheses are not read. Other goals, undecided equalities and
   goals with an evar fail. *)
Ltac zesu_bv_linear_refutes :=
  lazymatch goal with |- ?goal => tryif has_evar goal then fail 0 else idtac end;
  lazymatch goal with
  | |- @eq (bv _) ?lhs ?rhs =>
      assert_succeeds (assert (lhs <> rhs) by zesu_bv_linear_bv)
  | |- @eq Z (bv_unsigned ?lhs) (bv_unsigned ?rhs) =>
      assert_succeeds (assert (bv_unsigned lhs <> bv_unsigned rhs) by
        (apply (zesu_bv_unsigned_ne_of_ne lhs rhs); zesu_bv_linear_bv))
  | |- @eq Z (@bv_unsigned ?width ?term) ?value =>
      assert_succeeds (assert (bv_unsigned term <> value) by
        (apply (zesu_bv_unsigned_ne_of_cast (width := width) term value); zesu_bv_linear_bv))
  | |- @eq Z ?value (@bv_unsigned ?width ?term) =>
      assert_succeeds (assert (value <> bv_unsigned term) by
        (apply not_eq_sym; apply (zesu_bv_unsigned_ne_of_cast (width := width) term value);
         zesu_bv_linear_bv))
  end.
