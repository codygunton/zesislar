Require Import ZesuSsz.Automation.All.
From Coq Require Import List Lia.

Lemma finalListConsCloses {A : Type} (values : list A) count :
  length values = S count ->
  exists head tail, values = head :: tail /\ length tail = count.
Proof.
  intro Hlength.
  Fail solve [zesu_finish_pure_goal].
  solve [zesu_finish_final_pure].
Qed.

Lemma finalListConsWrongCount (values : list nat) :
  length values = 40%nat -> True.
Proof.
  intro Hlength.
  Fail assert (exists head tail, values = head :: tail /\ length tail = 40%nat)
    by solve [zesu_finish_list_cons_final].
  exact I.
Qed.

Lemma finalListConsEvar : True.
Proof.
  evar (values : list nat).
  let pending := eval unfold values in values in has_evar pending.
  Fail assert (exists head tail, values = head :: tail /\ length tail = 39%nat)
    by solve [zesu_finish_list_cons_final].
  let pending := eval unfold values in values in has_evar pending.
  let pending := eval unfold values in values in unify pending (@nil nat).
  exact I.
Qed.

Print Assumptions finalListConsCloses.
Print Assumptions finalListConsWrongCount.
Print Assumptions finalListConsEvar.
