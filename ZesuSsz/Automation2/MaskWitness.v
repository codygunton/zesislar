(* System-register witnesses (for example a saved status word) appear in
   generated entries as bitvector existentials that only pure low-bit facts
   constrain: `bv_and w M = 0`, its unsigned view, and the bit views of the
   same bits. A context word with `Z.land (bv_unsigned t) M = 0` satisfies
   them. The step instantiates such a telescope when its body holds no owned
   resource; the closer proves the facts from the context word. No rule names
   an address, register, or contract predicate. *)
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Automation2.BitvectorFacts.
From iris.proofmode Require Import environments tactics.
From stdpp Require Import bitvector.definitions bitvector.tactics.
From Coq Require Import ZArith.ZArith.
Local Open Scope Z_scope.

Ltac zesu_mask_word width continuation :=
  match goal with
  | H : Z.land (bv_unsigned ?word) ?mask = 0%Z |- _ =>
      lazymatch type of word with bv width => continuation word end
  end.

Ltac zesu_mask_witness_tuple T continuation :=
  lazymatch T with
  | unit => continuation constr:(tt)
  | li_prod (bv ?width) ?rest =>
      zesu_mask_word width ltac:(fun word =>
        zesu_mask_witness_tuple rest ltac:(fun tail => continuation constr:(li_pair word tail)))
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

(* Commit to the witnesses only when the closer proves every pure fact of
   the instantiated body, so the step never preempts another witness route. *)
Ltac zesu_mask_pure_closable body :=
  lazymatch body with
  | @bi_sep _ ?left ?right => zesu_mask_pure_closable left; zesu_mask_pure_closable right
  | @bi_pure _ ?fact =>
      assert_succeeds (idtac; let Hfact := fresh "HmaskFact" in
        assert (Hfact : fact) by zesu_mask_fact_close)
  | ?frame => is_var frame
  end.

Ltac zesu_mask_witness_telescope :=
  lazymatch goal with
  | |- envs_entails _ (@bi_exist _ ?T ?body) =>
      lazymatch T with li_prod _ _ => idtac end;
      zesu_mask_witness_tuple T ltac:(fun witness =>
        let instantiated := eval cbv beta iota delta [li_fst li_snd] in (body witness) in
        zesu_mask_pure_closable instantiated;
        notypeclasses refine (tac_ex_evar _ witness _ _); red_li_prod)
  end.
