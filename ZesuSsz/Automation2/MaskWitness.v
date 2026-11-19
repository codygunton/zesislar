(* System-register witnesses (for example a saved status word) appear in
   generated entries as bitvector existentials that only pure low-bit facts
   constrain: `bv_and w M = 0`, its unsigned view, and the bit views of the
   same bits. A context word with `Z.land (bv_unsigned t) M = 0` satisfies
   them; without one, a constant tuple whose facts computation decides does.
   The step instantiates such a telescope when no owned resource mentions its
   witnesses; the closer proves the witness facts, and the facts that do not
   mention the witnesses stay for the steps after the choice. No rule names
   an address, register, or contract predicate. *)
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Automation2.BitvectorFacts.
Require ZesuSsz.Automation2.VmClosed.
Require Import ZesuSsz.Automation2.LiaHook.
From iris.proofmode Require Import environments tactics.
From stdpp Require Import bitvector.definitions bitvector.tactics.
From Coq Require Import ZArith.ZArith.
Local Open Scope Z_scope.

(* The witness choice commits: one context word, no backtracking over the
   telescope's components. *)
Ltac zesu_mask_word width :=
  match goal with
  | H : Z.land (bv_unsigned ?word) ?mask = 0%Z |- _ =>
      lazymatch type of word with bv width => word end
  end.

Ltac zesu_mask_witness_tuple T :=
  lazymatch T with
  | unit => constr:(tt)
  | li_prod (bv ?width) ?rest =>
      let word := zesu_mask_word width in
      let tail := zesu_mask_witness_tuple rest in
      constr:(li_pair word tail)
  end.

Ltac zesu_mask_bit_zero bit word continuation :=
  match goal with
  | H : Z.land (bv_unsigned word) ?mask = 0%Z |- _ =>
      let index := eval vm_compute in (Z.of_N bit) in
      let Hzero := fresh "HmaskBitZero" in
      assert (Hzero : bv_extract bit 1 word = (0%bv : bv 1)) by
        (change bit with (Z.to_N index);
         apply (BitvectorFacts.zesu_single_bit_land_zero _ index word);
         [split; vm_compute; congruence | exact H]);
      continuation Hzero
  end.

Ltac zesu_mask_fact_close :=
  lazymatch goal with
  | |- bool_decide _ = true => apply bool_decide_eq_true_2; zesu_mask_fact_close
  | |- negb (bool_decide _) = true =>
      apply negb_true_iff, bool_decide_eq_false_2; zesu_mask_fact_close
  | |- _ /\ _ => split; zesu_mask_fact_close
  | |- @bv_and _ ?word _ = _ =>
      match goal with
      | H : Z.land (bv_unsigned word) _ = 0%Z |- _ =>
          apply bv_eq; rewrite bv_and_unsigned !bv_unsigned_BV; exact H
      end
  | |- bv_unsigned (@bv_and _ ?word _) = 0%Z =>
      match goal with
      | H : Z.land (bv_unsigned word) _ = 0%Z |- _ =>
          rewrite bv_and_unsigned bv_unsigned_BV; exact H
      end
  | |- ~ (bv_extract ?bit 1 ?word = _) =>
      zesu_mask_bit_zero bit word ltac:(fun Hzero => rewrite Hzero; discriminate)
  | |- bv_unsigned (bv_extract ?bit 1 ?word) <> 1%Z =>
      zesu_mask_bit_zero bit word ltac:(fun Hzero => rewrite Hzero; vm_compute; congruence)
  end.

(* A closed fact (a witness chosen as a constant) is decided by computation. *)
Ltac zesu_mask_closed_fact_close :=
  lazymatch goal with
  | |- ?fact =>
      ZesuSsz.Automation2.VmClosed.zesu_closed_term fact;
      first [vm_compute; reflexivity | apply (bool_decide_unpack _); vm_compute; reflexivity]
  end.

Ltac zesu_mask_witness_fact_close :=
  first [zesu_mask_fact_close | zesu_mask_closed_fact_close].

(* The constant candidate: every component zero. *)
Ltac zesu_mask_zero_tuple T :=
  lazymatch T with
  | unit => constr:(tt)
  | li_prod (bv ?width) ?rest =>
      let tail := zesu_mask_zero_tuple rest in
      constr:(li_pair (BV width 0) tail)
  end.

(* Guard on the conjuncts that do not mention the witnesses: each linear
   comparison among them must follow from the context by linear arithmetic.
   A telescope whose independent part carries a path fact the context states
   only in another form (one that a source route proves after the choice)
   is left to that route: committed here, the steps after the choice fail on
   that fact only after rebuilding the requested resources. *)
Ltac zesu_mask_independent_linear fact :=
  assert_succeeds (idtac; let Hindependent := fresh "HmaskIndependent" in
    assert (Hindependent : fact) by zesu_lia).

Ltac zesu_mask_independent_fact fact :=
  lazymatch fact with
  | ?left /\ ?right => zesu_mask_independent_fact left; zesu_mask_independent_fact right
  | (_ <= _)%Z => zesu_mask_independent_linear fact
  | (_ < _)%Z => zesu_mask_independent_linear fact
  | (_ >= _)%Z => zesu_mask_independent_linear fact
  | (_ > _)%Z => zesu_mask_independent_linear fact
  | _ => idtac
  end.

Ltac zesu_mask_independent independent :=
  lazymatch independent with
  | @bi_sep _ ?left ?right => zesu_mask_independent left; zesu_mask_independent right
  | @bi_pure _ ?fact => zesu_mask_independent_fact fact
  | _ => idtac
  end.

(* Walk the telescope's body under its binder. A conjunct that does not
   mention the witnesses is left to the steps after the choice (its linear
   comparisons guarded above); a pure conjunct that mentions them must close
   for the candidate; a resource that mentions them refuses the telescope,
   so the step never preempts a resource-driven witness route. *)
Ltac zesu_mask_pure_closable body witness :=
  lazymatch body with
  | (fun _ => ?independent) => zesu_mask_independent independent
  | (fun x => @bi_sep _ (@?left x) (@?right x)) =>
      zesu_mask_pure_closable left witness; zesu_mask_pure_closable right witness
  | (fun x => @bi_pure _ (@?fact x)) =>
      let instantiated := eval cbv beta iota delta [li_fst li_snd] in (fact witness) in
      assert_succeeds (idtac; let Hfact := fresh "HmaskFact" in
        assert (Hfact : instantiated) by zesu_mask_witness_fact_close)
  end.

Ltac zesu_mask_commit body witness :=
  zesu_mask_pure_closable body witness;
  notypeclasses refine (tac_ex_evar _ witness _ _); red_li_prod.

(* Candidates in order: a context word whose facts entail the conjuncts,
   then the constant zero tuple when computation decides the conjuncts. *)
Ltac zesu_mask_witness_telescope :=
  lazymatch goal with
  | |- envs_entails _ (@bi_exist _ ?T ?body) =>
      lazymatch T with li_prod _ _ => idtac end;
      first [let witness := zesu_mask_witness_tuple T in zesu_mask_commit body witness
            | let witness := zesu_mask_zero_tuple T in zesu_mask_commit body witness]
  end.
