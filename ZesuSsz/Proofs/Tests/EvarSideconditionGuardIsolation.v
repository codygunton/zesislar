Require Import ZesuSsz.Automation.All.
From Coq Require Import Arith.PeanoNat.

Lemma evar_sidecondition_disabled : True.
Proof.
  Fail let enabled := constr:(_ : ZesuStepEvarSideconditionGuard) in idtac.
  evar (index : nat).
  assert (Hindex : (index < 2)%nat).
  { Fail zesu_defer_unresolved_sidecondition_if_enabled.
    instantiate (index := 0%nat).
    exact (Nat.lt_0_succ 1). }
  exact I.
Qed.
