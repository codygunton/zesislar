From lithium Require Import definitions proof_state.
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Contracts.IslarisMemory.

(* An array that a continuation requests inside an uninitialized region, with
   a witness that the continuation leaves open (a callee's output buffer). The
   bytes of the region are only known after the split, so the witness is chosen
   after them; the length is chosen before, from a pure fact of the
   continuation. Without such a fact the step returns None and the rule
   continues as IslarisMemory.v's `subsume_mem_uninit_byte_array`. *)
Definition zesu_uninit_request_length {Sigma A} (requested : A -> list (bv 8))
    (G : A -> iProp Sigma) (T : option nat -> iProp Sigma) : iProp Sigma :=
  ∃ n, T n.
Arguments zesu_uninit_request_length : simpl never.
Global Typeclasses Opaque zesu_uninit_request_length.

Program Definition zesu_uninit_request_length_hint {Sigma A} requested G n :
  LiTactic (@zesu_uninit_request_length Sigma A requested G) := {|
    li_tactic_P T := T n;
|}.
Next Obligation. intros. unfold zesu_uninit_request_length. iIntros "?". iExists _. iFrame. Qed.

(* The body of a continuation that Lithium let-bound. *)
Ltac zesu_uninit_request_unlet term :=
  match goal with
  | H := LET_ID ?T |- _ => match constr:((H, term)) with (?a, ?a) => T end
  | _ => term
  end.

(* A fact that, unfolded at each head, states `length target = N` for a closed
   N among its conjuncts; N is unified with the let-bound evar `hole`. Only the
   measured list is compared: the element type of `length` may sit behind an
   alias on either side. *)
Ltac zesu_uninit_request_length_in fact target hole :=
  let fact := eval hnf in fact in
  lazymatch fact with
  | ?left /\ ?right =>
      first [zesu_uninit_request_length_in left target hole
            | zesu_uninit_request_length_in right target hole]
  | @eq nat ?lhs ?rhs =>
      let lhs := eval cbn in lhs in
      lazymatch lhs with
      | @length _ ?measured =>
          let wanted := eval cbn in target in
          constr_eq measured wanted;
          assert_fails (has_evar rhs);
          let evar_hole := eval unfold hole in hole in
          unify evar_hole rhs
      end
  end.

Ltac zesu_uninit_request_length_solve :=
  lazymatch goal with
  | |- LiTactic (@zesu_uninit_request_length _ ?A ?requested ?G) =>
      first [
        let N := fresh "N" in
        evar (N : nat);
        let found := fresh "found" in
        assert (found : forall y : A, True);
        [ intros y;
          let body := zesu_uninit_request_unlet G in
          let continuation := eval cbv beta in (body y) in
          let target := eval cbv beta in (requested y) in
          match continuation with
          | context [@bi_pure _ ?fact] => zesu_uninit_request_length_in fact target N
          end; exact I
        | clear found;
          let n := eval unfold N in N in
          clear N; exact (zesu_uninit_request_length_hint requested G (Some n)) ]
      | exact (zesu_uninit_request_length_hint requested G None) ]
  end.
Global Hint Extern 10 (LiTactic (zesu_uninit_request_length _ _)) =>
  zesu_uninit_request_length_solve : typeclass_instances.

(* The continuation for a chosen length, or IslarisMemory.v's premise. *)
Definition zesu_uninit_request_case `{!islaG Sigma} {A} (a1 a2 n1 : Z)
    (requested : A -> list (bv 8)) (G : A -> iProp Sigma) (choice : option nat) :
    iProp Sigma :=
  match choice with
  | Some n2 =>
      ⌜(a1 <= a2 ∧ a2 + n2 <= a1 + n1)%Z⌝ ∗
      (a1 ↦ₘ? (a2 - a1) -∗
      (a2 + n2) ↦ₘ? (a1 + n1 - (a2 + n2)) -∗
      ∀ values : list (bv 8),
        ⌜length values = n2⌝ -∗
        ∃ x, ⌜requested x = values⌝ ∗ G x)
  | None =>
      ∃ x,
      let n2 := Z.of_nat (length (requested x)) in
      ⌜(0 <= n2 ∧ a1 <= a2 ∧ a2 + n2 <= a1 + n1)%Z⌝ ∗
      (a1 ↦ₘ? (a2 - a1) -∗
      (a2 + n2) ↦ₘ? (a1 + n1 - (a2 + n2)) -∗
      ∀ values : list (bv 8),
        ⌜Z.of_nat (length values) = n2⌝ -∗
        ⌜requested x = values⌝ ∗ G x)
  end%I.
Global Instance : LithiumUnfold (@zesu_uninit_request_case) := I.
Global Typeclasses Opaque zesu_uninit_request_case.

Section uninitialized_request_subsumption.
  Context `{!islaG Sigma}.

  Lemma subsume_mem_uninit_request A a1 a2 n1
      (requested : A -> list (bv 8)) G :
    li_tactic (zesu_uninit_request_length requested G)
      (zesu_uninit_request_case a1 a2 n1 requested G)
    ⊢ subsume (a1 ↦ₘ? n1) (fun x : A => a2 ↦ₘ∗ requested x) G.
  Proof.
    iIntros "Hrule Hmemory".
    unfold li_tactic, zesu_uninit_request_length.
    iDestruct "Hrule" as ([n2|]) "Hrule"; cbn [zesu_uninit_request_case].
    - iDestruct "Hrule" as (Hbounds) "Hcontinue".
      iDestruct (mem_mapsto_uninit_split (a2 - a1) with "Hmemory") as
        "[Hprefix Hrest]"; [lia |].
      have Hbase : (a1 + (a2 - a1) = a2)%Z by lia.
      iEval (rewrite Hbase) in "Hrest".
      iDestruct (mem_mapsto_uninit_split n2 with "Hrest") as
        "[Hregion Hsuffix]"; [lia |].
      iDestruct (mem_mapsto_uninit_to_byte_array with "Hregion") as
        (values Hlength) "Hregion".
      iDestruct ("Hcontinue" with "Hprefix [Hsuffix]") as "Hcontinue".
      { replace (n1 - (a2 - a1) - n2)%Z with
          (a1 + n1 - (a2 + n2))%Z by lia.
        iExact "Hsuffix". }
      iDestruct ("Hcontinue" $! values with "[]") as (x Hrequested) "Hcontinue".
      { iPureIntro. lia. }
      iExists x. rewrite Hrequested. iFrame.
    - iApply (subsume_mem_uninit_byte_array with "Hrule Hmemory").
  Qed.

  Definition subsume_mem_uninit_request_inst :=
    [instance @subsume_mem_uninit_request].
  Global Existing Instance subsume_mem_uninit_request_inst | 89.
End uninitialized_request_subsumption.
