(* Exact shared-suffix equations determine the row and empty prefix.
   The search preserves the Iris environment and stops after 32 steps.
   Spatial heads require LithiumUnfold. Pure heads reduce only to a
   conjunction, as in zesu_split_folded_pure. *)
Require Import ZesuSsz.Automation.TracePrefixTail.
Require Import isla.riscv64.riscv64.
From iris.proofmode Require Import environments.

Ltac zesu_shared_suffix_pure fuel facts row_marker prefix_marker accept :=
  lazymatch fuel with
  | O => fail 0 "No exact shared-suffix equation"
  | S ?remaining =>
      lazymatch facts with
      | ?row :: ?suffix = prefix_marker ++ row_marker :: ?other =>
          assert_fails (has_evar row);
          assert_fails (has_evar suffix);
          assert_fails (has_evar other);
          constr_eq suffix other;
          assert_fails (constr_eq row row_marker);
          accept row
      | ?left /\ ?right =>
          first [zesu_shared_suffix_pure remaining left row_marker prefix_marker accept
                | zesu_shared_suffix_pure remaining right row_marker prefix_marker accept]
      | _ =>
          lazymatch type of facts with Prop => idtac end;
          assert_fails (has_evar facts);
          let opened := eval hnf in facts in
          lazymatch opened with
          | _ /\ _ =>
              zesu_shared_suffix_pure remaining opened row_marker prefix_marker accept
          end
      end
  end.

Ltac zesu_shared_suffix_equation fuel body row_marker prefix_marker accept :=
  lazymatch fuel with
  | O => fail 0 "No exact shared-suffix equation"
  | S ?remaining =>
      lazymatch body with
      | (⌜?facts⌝)%I =>
          zesu_shared_suffix_pure remaining facts row_marker prefix_marker accept
      | (?left ∗ ?right)%I =>
          first [zesu_shared_suffix_equation remaining left row_marker prefix_marker accept
                | zesu_shared_suffix_equation remaining right row_marker prefix_marker accept]
      | _ =>
          let head := get_head body in
          let _ := constr:(_ : LithiumUnfold head) in
          let opened := eval cbv beta zeta delta [head] in body in
          zesu_shared_suffix_equation remaining opened row_marker prefix_marker accept
      end
  end.

Ltac zesu_select_shared_suffix_tuple :=
  let _ := constr:(_ : ZesuStepTracePrefixTail) in
  lazymatch goal with
  | |- envs_entails _
      (@bi_exist _ (li_prod (list (bv 8))
        (li_prod (list (list (bv 8))) unit)) ?body) =>
      let row_marker := fresh "sharedSuffixRow" in
      let prefix_marker := fresh "sharedSuffixPrefix" in
      pose (row_marker := ([] : list (bv 8)));
      pose (prefix_marker := ([] : list (list (bv 8))));
      let witness := constr:((row_marker, prefix_marker, tt)ₗ) in
      let opened := eval cbv beta iota delta [li_fst li_snd] in (body witness) in
      zesu_shared_suffix_equation 32 opened row_marker prefix_marker
        ltac:(fun row => iExists (row, ([] : list (list (bv 8))), tt)ₗ;
          clear row_marker prefix_marker)
  end.
