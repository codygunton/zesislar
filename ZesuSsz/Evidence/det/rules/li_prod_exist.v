(* Candidate rule: split a `li_prod` existential whose body uses the
   variable.

   Lithium's `liExist` ends with `fail "not handled by liExist"` for
   `∃ x : A *ₗ B, body x` (lithium/interpreter.v), and that is the shape
   every call with an open trace leaves. Splitting the product hands the
   goal back to Lithium, which instantiates each component with an evar.

   The first version reduced the projections with `red_li_prod`
   (`cbv [li_fst li_snd]`), a full traversal of a goal that carries the
   whole event history, inside a `repeat`. Wired into the automation that
   way it took `check-iris` past the 200 GiB batch cap. This version
   rewrites the two projection equations instead of normalizing. *)

Section zesu_li_prod_candidate.
  Context {Sigma : gFunctors}.

  (* `.2ₗ` is not the second projection: in Lithium a product is a chain,
     so `x.2ₗ` means `x.nextₗ.1ₗ`. The projections themselves are the
     record fields. *)
  Lemma zesu_li_fst_pair {A B} (a : A) (b : B) : @li_fst A B (a, b)ₗ = a.
  Proof. reflexivity. Qed.

  Lemma zesu_li_snd_pair {A B} (a : A) (b : B) : @li_snd A B (a, b)ₗ = b.
  Proof. reflexivity. Qed.

  Lemma tac_zesu_li_prod_exist_candidate {A B} Delta
      (Phi : li_prod A B → iProp Sigma) :
    envs_entails Delta (∃ (a : A) (b : B), Phi (a, b)ₗ) →
    envs_entails Delta (∃ x : li_prod A B, Phi x).
  Proof.
    rewrite envs_entails_unseal => Hgoal. etrans; [exact Hgoal|].
    iIntros "(%a & %b & H)". by iExists (a, b)ₗ.
  Qed.
End zesu_li_prod_candidate.

Ltac zesu_open_li_prod_candidate :=
  lazymatch goal with
  | |- envs_entails _ (@bi_exist _ (li_prod _ _) _) =>
      notypeclasses refine (tac_zesu_li_prod_exist_candidate _ _ _);
      rewrite ?zesu_li_fst_pair ?zesu_li_snd_pair
  end.
