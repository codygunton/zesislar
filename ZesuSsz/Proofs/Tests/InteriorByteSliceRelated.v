From Coq Require Import Lists.List.
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Automation2.InteriorByteSlice.
Require Import ZesuSsz.Automation2.All.
Local Open Scope Z_scope.

(* An array is a lend candidate only if the slice address is reached from
   its base word or a fact places a word on the address's way inside its
   bytes. Other arrays are skipped before any arithmetic. *)
Section related.
Context (base other cursor word : bv 64) (bytes junk : list (bv 8)).
Context (P : list (bv 8) -> Prop).
Context (Hinside : P (drop (Z.to_nat (bv_unsigned cursor - bv_unsigned base)) bytes)).

Goal True.
Proof using All.
  zesu_byte_slice_related (bv_unsigned base + 8) (bv_unsigned base) bytes.
  zesu_byte_slice_related (bv_unsigned (base + word)%bv) (bv_unsigned base) bytes.
  Fail zesu_byte_slice_related (bv_unsigned base + 8) (bv_unsigned other) junk.
  (* A kept cursor: reached through the fact over the array's bytes. *)
  zesu_byte_slice_related (bv_unsigned (cursor + word)%bv) (bv_unsigned other) bytes.
  Fail zesu_byte_slice_related (bv_unsigned (cursor + word)%bv) (bv_unsigned other) junk.
  pose (kept := (cursor + word)%bv).
  zesu_byte_slice_related (bv_unsigned kept) (bv_unsigned other) bytes.
  exact I.
Qed.
End related.

(* The lend skips an unrelated array that precedes the owning one. *)
Section skip.
Context `{!islaG Sigma} `{!threadG}.
Lemma test_interior_byte_slice_skips_unrelated (base other : Z) (bytes junk : list (bv 8)) :
  length bytes = 64%nat -> length junk = 64%nat ->
  base ↦ₘ∗ bytes -∗ other ↦ₘ∗ junk -∗
  ∃ x : list (bv 8) *ₗ (),
    (base + 8) ↦ₘ∗ x.1ₗ ∗ ⌜16 = Z.of_nat (length x.1ₗ)⌝ ∗
    ((base + 8) ↦ₘ∗ x.1ₗ -∗ base ↦ₘ∗ bytes) ∗ other ↦ₘ∗ junk.
Proof.
  iIntros (Hbytes Hjunk) "Harray Hother".
  zesu_lend_interior_byte_slice.
  cbn [li_fst]. iFrame. iPureIntro.
  rewrite length_take length_drop. lia.
Qed.
End skip.

(* The side goals of a lend see the facts over the goal's value words (local
   definitions read through) and the facts over contract arguments alone;
   a fact over other words only is cleared. *)
Record FocusArgs := { focusPointer : bv 64 }.
Goal forall (args : FocusArgs) (x y z : Z),
  y = 2 -> 0 <= bv_unsigned (focusPointer args) -> z = 3 ->
  let w := z + 1 in x = z + 1 -> x = w.
Proof.
  intros args x y z Hy Hpointer Hz w Hx.
  ltac2:(zesu_byte_slice_focus ()).
  tryif (match goal with _ : y = 2 |- _ => idtac end) then fail else idtac.
  match goal with _ : 0 <= bv_unsigned (focusPointer args) |- _ => idtac end.
  match goal with _ : z = 3 |- _ => idtac end.
  unfold w. lia.
Qed.
