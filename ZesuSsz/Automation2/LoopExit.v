Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Automation2.BitvectorFacts.
Require ZesuSsz.Automation2.MaskWitness.
From iris.proofmode Require Import environments tactics.
From stdpp Require Import bitvector.definitions bitvector.tactics.
From Coq Require Import ZArith.ZArith Lia Bool.
Local Open Scope Z_scope.

(* The cursor range that the load rule records implies the list index of the
   load. The two sides may count the elements at convertible element types
   (`bv 8` in the index goal, `byte` in the range fact): `lia` sees two
   `length` atoms, the lemma one. *)
Lemma zesu_cursor_index {A} (l : list A) (c ip : Z) :
  ip <= c < ip + Z.of_nat (length l) ->
  (Z.to_nat ((c - ip) `div` 1) < length l)%nat.
Proof. intros Hrange. rewrite Z.div_1_r. lia. Qed.

Ltac zesu_cursor_index_close :=
  lazymatch goal with
  | |- (Z.to_nat ((?c - ?ip) `div` 1) < length _)%nat =>
      match goal with
      | H : ip <= c < ip + _ |- _ => exact (zesu_cursor_index _ _ _ H)
      end
  end.

(* Views of the facts a loop exit hands to its successor. The loop class keeps
   a guard in the form the branch decided it (a boolean, a signed compare of a
   zero-extended word, a word against zero); the successor entry states the
   unsigned view next to it. Each lemma derives one view from one guard. *)
Lemma zesu_exit_view_zext_zero (n : N) (w : bv n) :
  (n <= 64)%N -> bv_zero_extend 64 w = (BV 64 0) -> bv_unsigned w = 0.
Proof.
  intros Hle Hzero. rewrite <- (bv_zero_extend_unsigned 64 w) by exact Hle. rewrite Hzero. reflexivity.
Qed.

Lemma zesu_exit_view_ne_zero (w : bv 64) : w <> BV 64 0 -> bv_unsigned w <> 0.
Proof. intros Hne Hzero. apply Hne. apply bv_eq. exact Hzero. Qed.

Lemma zesu_exit_view_byte_lo (b : bv 8) : 0 <= bv_unsigned b.
Proof. pose proof (bv_unsigned_in_range _ b). lia. Qed.

Lemma zesu_exit_view_byte_hi (b : bv 8) : bv_unsigned b <= 255.
Proof.
  pose proof (bv_unsigned_in_range _ b) as H. unfold bv_modulus in H.
  change (2 ^ Z.of_N 8) with 256 in H. lia.
Qed.

Lemma zesu_exit_view_signed_ge (w : bv 64) (k : bv 128) :
  bv_signed k >= bv_signed (bv_zero_extend 128 w) -> bv_signed k >= bv_unsigned w.
Proof. rewrite zesu_signed_zero_extend_64_128. tauto. Qed.

Lemma zesu_exit_view_signed_not_lt (w : bv 64) (k : bv 128) :
  ~ bv_signed k < bv_signed (bv_zero_extend 128 w) -> bv_signed k >= bv_unsigned w.
Proof. rewrite zesu_signed_zero_extend_64_128. lia. Qed.

(* One pure conjunct of the successor entry, after the witnesses are constants. *)
Ltac zesu_exit_fact :=
  first
  [ assumption
  | apply bool_decide_eq_true_2; assumption
  | apply negb_true_iff, bool_decide_eq_false_2; assumption
  | solve [ZesuSsz.Automation2.MaskWitness.zesu_mask_closed_fact_close]
  | eapply zesu_exit_view_zext_zero; [vm_compute; discriminate | eassumption]
  | match goal with H : ?w = _ |- bv_unsigned ?w = _ => exact (f_equal bv_unsigned H) end
  | apply zesu_exit_view_ne_zero; assumption
  | apply zesu_exit_view_byte_lo
  | apply zesu_exit_view_byte_hi
  | match goal with
    | H : bv_signed ?k >= bv_signed (bv_zero_extend 128 ?w) |- _ >= bv_unsigned ?w =>
        exact (zesu_exit_view_signed_ge w k H)
    | H : ~ bv_signed ?k < bv_signed (bv_zero_extend 128 ?w) |- _ >= bv_unsigned ?w =>
        exact (zesu_exit_view_signed_not_lt w k H)
    end ].

(* Ghost witnesses constrained only by pure facts: commit the constant zero
   tuple without asking that every conjunct is closed for it; the conjuncts
   are then proved one by one. *)
Ltac zesu_exit_zero_witnesses :=
  lazymatch goal with
  | |- envs_entails _ (@bi_exist _ ?T _) =>
      let witness := ZesuSsz.Automation2.MaskWitness.zesu_mask_zero_tuple T in
      notypeclasses refine (tac_ex_evar _ witness _ _); red_li_prod
  end.

Ltac zesu_exit_split :=
  repeat iSplit;
  lazymatch goal with
  | |- envs_entails _ (bi_pure _) => iPureIntro
  | |- _ => idtac
  end.

(* The exit step: zero witnesses, then every conjunct is a view of a guard or a
   resource of the context. *)
Ltac zesu_loop_exit_witnesses :=
  solve [zesu_exit_zero_witnesses; zesu_exit_split; first [zesu_exit_fact | iFrame]].
