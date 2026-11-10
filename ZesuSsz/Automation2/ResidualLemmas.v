(* Residual lemmas: the pure tier after the selected-facts solvers.

   A residual module (ZesuSsz/Residuals/<Block>.v) exports exact lemmas for
   the pure goals that the solvers leave open in one block. Each lemma binds
   the goal's variables universally and takes the selected facts as premises.
   The tier applies one lemma whose conclusion matches the goal and closes its
   premises from the context. The search is depth bounded; an empty database
   fails at once. *)
Create HintDb zesu_residual discriminated.
#[export] Hint Constants Opaque : zesu_residual.
#[export] Hint Variables Opaque : zesu_residual.

(* Depth 2: one residual lemma, then each premise by assumption. *)
Ltac zesu_residual_lemma := solve [eauto 2 with nocore zesu_residual].
