(** A named equation: the generator gave the name [name] to the value [value].

    The marker is an inductive, so no tactic sees it as an equation: Lithium's
    [subst] keeps the name, and conversion, [hnf] and [simpl] never expose the
    value. A rule that needs the value opens the marker with
    [zesu_named_eq_iff], inside the goal it is solving. *)
Inductive zesu_named_eq {A : Type} (name value : A) : Prop :=
  zesu_named_eq_intro : name = value -> zesu_named_eq name value.

Lemma zesu_named_eq_iff {A : Type} (name value : A) :
  zesu_named_eq name value <-> name = value.
Proof. split; [intros [equality]; exact equality | exact (zesu_named_eq_intro name value)]. Qed.

From Coq Require Import ZArith.

(** A call's output buffer, as the call's own block declares it: the call's argument address
    [call_address] (the term the call computes) is the region's address [declared] (the form the
    return site states). The block's predecessor proves the equation. *)
Definition zesu_call_address (call_address declared : Z) : Prop := call_address = declared.
