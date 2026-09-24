(* Opt-in T1 rule: use a known list lookup before comparing trace payloads. *)
Require Import isla.riscv64.riscv64.

Lemma zesu_loaded_word_default {A : Type} (words : list A) (index : nat)
    (fallback word : A) :
  words !! index = Some word -> default fallback (words !! index) = word.
Proof. intros Hlookup. by rewrite Hlookup. Qed.

Print Assumptions zesu_loaded_word_default.

Ltac zesu_rewrite_loaded_word :=
  repeat match goal with
  | Hlookup : ?words !! ?index = Some ?word
    |- context [default ?fallback (?words !! ?index)] =>
      rewrite (zesu_loaded_word_default words index fallback word Hlookup)
  end.

Class ZesuStepLoadedWordTrace : Prop := zesu_step_loaded_word_trace : True.

Ltac zesu_rewrite_loaded_word_if_enabled :=
  lazymatch goal with
  | Hlookup : ?words !! ?index = Some ?word
    |- context [default ?fallback (?words !! ?index)] =>
      let _ := constr:(_ : ZesuStepLoadedWordTrace) in
      zesu_rewrite_loaded_word
  end.
