Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Automation2.InteriorByteSlice.
Require Import ZesuSsz.Automation2.All.
Local Open Scope Z_scope.

(* A callee's domain states its input's length among other facts, behind a
   definition; the length is a symbolic size, not a constant. *)
Definition slice_request_domain (size : Z) (input other : list (bv 8)) : Prop :=
  0 <= size /\ size = Z.of_nat (length input) /\ length other = 8%nat.

(* The step reads the size from the domain and lends the interior slice. *)
Lemma test_interior_byte_slice_domain `{!islaG Sigma} `{!threadG}
    (base start size : Z) (bytes other : list (bv 8)) :
  0 <= start -> 0 <= size -> start + size <= Z.of_nat (length bytes) ->
  length other = 8%nat ->
  base ↦ₘ∗ bytes -∗
  ∃ x : list (bv 8) *ₗ (),
    (base + start) ↦ₘ∗ x.1ₗ ∗
    ⌜slice_request_domain size x.1ₗ other⌝ ∗
    ((base + start) ↦ₘ∗ x.1ₗ -∗ base ↦ₘ∗ bytes).
Proof.
  iIntros (Hstart Hsize Hfits Hother) "Harray".
  zesu_lend_interior_byte_slice.
  cbn [li_fst]. iFrame. iPureIntro.
  unfold slice_request_domain. rewrite length_take length_drop. lia.
Qed.
Print Assumptions test_interior_byte_slice_domain.

(* The size is the one the domain states for the slice; a domain that states
   a size only for another list gives the slice none. *)
Goal forall (size : Z) (input other : list (bv 8)), True.
Proof.
  intros size input other.
  let found := zesu_byte_slice_size_in (slice_request_domain size input other) input in
  constr_eq found size.
  Fail let found := zesu_byte_slice_size_in (slice_request_domain size other input) input in
  idtac.
  exact I.
Qed.
