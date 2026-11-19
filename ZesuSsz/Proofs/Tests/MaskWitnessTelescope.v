Require Import isla.riscv64.riscv64.
From Coq Require Import ZArith.
From iris.proofmode Require Import environments tactics.
Require Import ZesuSsz.Automation2.All.
Local Open Scope Z_scope.

(* The telescope step before the binder walk: it instantiated the body with
   a context word and required every conjunct to be a closable mask fact or
   a frame variable. *)
Ltac previous_mask_pure_closable body :=
  lazymatch body with
  | @bi_sep _ ?left ?right => previous_mask_pure_closable left; previous_mask_pure_closable right
  | @bi_pure _ ?fact =>
      assert_succeeds (idtac; let Hfact := fresh "HmaskFact" in
        assert (Hfact : fact) by MaskWitness.zesu_mask_fact_close)
  | ?frame => is_var frame
  end.

Ltac previous_mask_witness_telescope :=
  lazymatch goal with
  | |- envs_entails _ (@bi_exist _ ?T ?body) =>
      lazymatch T with li_prod _ _ => idtac end;
      let witness := MaskWitness.zesu_mask_witness_tuple T in
      let instantiated := eval cbv beta iota delta [li_fst li_snd] in (body witness) in
      previous_mask_pure_closable instantiated;
      notypeclasses refine (tac_ex_evar _ witness _ _); red_li_prod
  end.

Section mask_tests.
  Context `{!islaG Sigma} `{!threadG}.

  (* An owned resource and a pure fact that do not mention the witness stay
     for the steps after the choice. *)
  Lemma mask_independent_conjuncts (status : bv 64) (a : Z) (v : bv 8) (x : Z)
      (Hstatus : Z.land (bv_unsigned status) 8 = 0) (Hx : x = 3) :
    a ↦ₘ v -∗
    ∃ p : bv 64 *ₗ unit,
      ⌜bv_and p.1ₗ (BV 64 8) = BV 64 0⌝ ∗ a ↦ₘ v ∗ ⌜x = 3⌝.
  Proof.
    iIntros "Hcell".
    Fail previous_mask_witness_telescope.
    MaskWitness.zesu_mask_witness_telescope.
    iSplit; [iPureIntro; MaskWitness.zesu_mask_fact_close |].
    iSplitL "Hcell"; [iExact "Hcell" | iPureIntro; exact Hx].
  Qed.

  (* Without a context word, the zero tuple whose facts computation decides. *)
  Lemma mask_zero_tuple :
    ⊢@{iProp Sigma} ∃ p : bv 64 *ₗ bv 64 *ₗ unit,
      ⌜bv_and p.1ₗ (BV 64 8) = BV 64 0⌝ ∗ ⌜bv_unsigned (bv_and p.2ₗ (BV 64 6)) = 0⌝.
  Proof.
    iStartProof.
    Fail previous_mask_witness_telescope.
    MaskWitness.zesu_mask_witness_telescope.
    iSplit; iPureIntro; MaskWitness.zesu_mask_closed_fact_close.
  Qed.

  (* A context word is preferred over the zero tuple. *)
  Lemma mask_context_word_first (status : bv 64)
      (Hstatus : Z.land (bv_unsigned status) 8 = 0) :
    ⊢@{iProp Sigma} ∃ p : bv 64 *ₗ unit, ⌜bv_and p.1ₗ (BV 64 8) = BV 64 0⌝.
  Proof.
    iStartProof.
    MaskWitness.zesu_mask_witness_telescope.
    lazymatch goal with
    | |- envs_entails _ (⌜bv_and status (BV 64 8) = BV 64 0⌝)%I => idtac
    end.
    iPureIntro. MaskWitness.zesu_mask_fact_close.
  Qed.

  (* A resource that mentions the witness refuses the telescope. *)
  Lemma mask_resource_mentions_witness (a : Z) (v : bv 64)
      (Hv : Z.land (bv_unsigned v) 8 = 0) :
    a ↦ₘ v -∗ ∃ p : bv 64 *ₗ unit, a ↦ₘ p.1ₗ ∗ ⌜bv_and p.1ₗ (BV 64 8) = BV 64 0⌝.
  Proof.
    iIntros "Hcell".
    Fail MaskWitness.zesu_mask_witness_telescope.
    iExists (li_pair v tt). cbv [li_fst li_snd].
    iFrame "Hcell". iPureIntro. MaskWitness.zesu_mask_fact_close.
  Qed.

  (* A witness fact that neither candidate satisfies refuses the telescope. *)
  Lemma mask_unsatisfied_fact :
    ⊢@{iProp Sigma} ∃ p : bv 64 *ₗ unit, ⌜bv_and p.1ₗ (BV 64 1) = BV 64 1⌝.
  Proof.
    iStartProof.
    Fail MaskWitness.zesu_mask_witness_telescope.
    iExists (li_pair (BV 64 1) tt). iPureIntro. apply bv_eq. vm_compute. reflexivity.
  Qed.
End mask_tests.
