(* Opt-in congruence for a trace payload defined by a successful lookup. *)
Require Import isla.isla.
From stdpp Require Import list.
From iris.proofmode Require Import environments.

Lemma zesu_scons_snap_loaded_lookup {A} (words : list A) (index : nat)
    (fallback loaded : A) (event : seq_event)
    (accept : A -> seq_snapshot -> Prop) (tail : spec) :
  words !! index = Some loaded ->
  scons_snap event (accept loaded) tail ⊆
    scons_snap event (accept (default fallback (words !! index))) tail.
Proof.
  intros Hlookup.
  rewrite Hlookup.
  simpl.
  reflexivity.
Qed.

(* Every loaded word, not the first: a block that loads several words
   holds one `Hlookup` per word, and the inclusion names one of them.
   `match` backtracks over the hypotheses until one fits the payload. *)
Ltac zesu_close_loaded_lookup :=
  match goal with
  | Hlookup : ?words !! ?index = Some ?loaded
    |- scons_snap ?event ?payload ?tail ⊆ _ =>
      lazymatch goal with
      | |- context[default ?fallback (?words !! ?index)] =>
          let abstracted := eval pattern loaded in payload in
          lazymatch abstracted with
          | ?accept ?loaded =>
              exact (zesu_scons_snap_loaded_lookup words index fallback loaded
                event accept tail Hlookup)
          end
      end
  end.

Class ZesuStepLoadedTrace : Prop := zesu_step_loaded_trace : True.

Ltac zesu_close_loaded_trace_if_enabled :=
  let _ := constr:(_ : ZesuStepLoadedTrace) in
  lazymatch goal with
  | |- envs_entails _ (@bi_exist _ (li_prod spec unit) _) =>
      iExists (_, tt)ₗ
  | |- envs_entails _ (@bi_exist _ (li_prod spec _) _) =>
      iExists (_, _)ₗ
  end;
  iSplit; [iPureIntro; zesu_close_loaded_lookup |].
