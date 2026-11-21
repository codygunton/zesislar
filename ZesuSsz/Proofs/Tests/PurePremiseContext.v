Require Import isla.riscv64.riscv64.
From iris.proofmode Require Import proofmode environments.
From Coq Require Import ZArith.
Require Import ZesuSsz.Automation2.All.
Local Open Scope Z_scope.

(* `zesu_pure_premise_from_context` (Finish.v): a pure premise that is
   literally a hypothesis is taken first; the rest of the goal is unchanged. *)
Lemma pure_premise_in_context {PROP : bi} Δ (a b : Z) (Q : PROP)
    (Hab : zesu_named_eq a (b + 1)) (HQ : envs_entails Δ Q) :
  envs_entails Δ (⌜zesu_named_eq a (b + 1)%Z⌝ ∗ Q).
Proof.
  ZesuSsz.Automation2.Finish.zesu_pure_premise_from_context.
  lazymatch goal with |- envs_entails Δ Q => exact HQ end.
Qed.

(* Absent: a hypothesis equal only up to conversion is not taken. *)
Lemma pure_premise_absent {PROP : bi} Δ (a b : Z) (Q : PROP)
    (Hab : zesu_named_eq a (1 + b)) (HQ : envs_entails Δ Q) :
  envs_entails Δ (⌜zesu_named_eq a (b + 1)%Z⌝ ∗ Q).
Proof.
  Fail ZesuSsz.Automation2.Finish.zesu_pure_premise_from_context.
  apply ZesuSsz.Automation2.Finish.tac_zesu_pure_premise_context; [|exact HQ].
  apply zesu_named_eq_iff. apply zesu_named_eq_iff in Hab. lia.
Qed.

(* An evar in the premise: the step refuses and leaves the evar open, although
   a hypothesis would unify with it. *)
Lemma pure_premise_evar {PROP : bi} Δ (a : Z) (Q : PROP)
    (Ha : a = 0) (HQ : envs_entails Δ Q) :
  exists n : Z, envs_entails Δ (⌜n = 0⌝ ∗ Q).
Proof.
  eexists.
  Fail ZesuSsz.Automation2.Finish.zesu_pure_premise_from_context.
  lazymatch goal with |- envs_entails _ (⌜?n = 0⌝ ∗ _) => is_evar n end.
  instantiate (1 := a).
  ZesuSsz.Automation2.Finish.zesu_pure_premise_from_context.
  exact HQ.
Qed.
