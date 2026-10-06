Require Import ZesuSsz.Automation.All.
Require Import ZesuSsz.Automation.BitvectorFacts.
Require Import isla.riscv64.riscv64.

Lemma stack_selected_once (x y : Z) (H : (x + (3 + 4) <= y)%Z) : True.
Proof.
  exactly_once (zesu_stack_normalize_hypothesis H).
  change (x + 7 <= y)%Z in H.
  Fail progress (zesu_stack_normalize_hypothesis H).
  exact I.
Qed.

Lemma stack_selected_aliases (x y : Z)
  (H : (x + (let k := 3 in k + 4) <= y)%Z) : True.
Proof.
  pose (three := 3%Z).
  pose (four := 4%Z).
  change (x + (let k := three in k + four) <= y)%Z in H.
  exactly_once (zesu_stack_normalize_hypothesis H).
  change (x + 7 <= y)%Z in H.
  exact I.
Qed.

Lemma stack_selected_pending (x : Z) : x = x.
Proof.
  evar (pending : Z).
  assert (Hpending : (pending + (3 + 4) = pending + 7)%Z) by reflexivity.
  zesu_stack_normalize_hypothesis Hpending.
  let value := eval unfold pending in pending in is_evar value.
  instantiate (pending := x).
  reflexivity.
Qed.

Lemma stack_selected_rollback (x y : Z) (H : (x + (3 + 4) <= y)%Z) : True.
Proof.
  try (zesu_stack_normalize_hypothesis H; fail 0).
  progress (zesu_stack_normalize_hypothesis H).
  Fail progress (zesu_stack_normalize_hypothesis H).
  exact I.
Qed.

Lemma stack_selected_symbolic (x y : Z) (H : (x + y <= y + x)%Z) : True.
Proof.
  Fail progress (zesu_stack_normalize_hypothesis H).
  exact I.
Qed.

Lemma stack_selected_rewrite (value : bv 64)
  (H : (bv_signed (bv_zero_extend 128 value + 8) <= 3221225472)%Z) : True.
Proof.
  zesu_stack_normalize_hypothesis H.
  rewrite (zesu_signed_zero_extend_add_64_128 value 8) in H; last bv_solve.
  exact I.
Qed.

Lemma stack_selected_shared (x y : Z)
  (Hleft : (x + (3 + 4) <= y)%Z) (Hright : (y <= x + (3 + 4))%Z) :
  (x + (3 + 4) = y)%Z.
Proof.
  exactly_once (zesu_stack_normalize_hypothesis Hleft).
  change (x + 7 <= y)%Z in Hleft.
  change (y <= x + 7)%Z in Hright.
  Fail progress (zesu_stack_normalize_hypothesis Hright).
  bv_solve.
Qed.
