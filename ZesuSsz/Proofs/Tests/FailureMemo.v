From Coq Require Import ZArith.ZArith.
From Ltac2 Require Import Ltac2.
Require Import ZesuSsz.Automation2.FailureMemo.
Require Import ZesuSsz.Automation2.All.
Set Default Proof Mode "Classic".
Local Open Scope Z_scope.

(* A memo site stands for one tactic. Here two different tactics share a site
   name, so a recorded failure shows: the second tactic would succeed, and
   the memo fails it at once on the same goal and context. *)
Ltac zesu_test_memo tac :=
  let run := ltac2:(tac |- zesu_failure_memo_ltac1 "zesu_test_memo" tac) in
  run tac.
Ltac zesu_test_memo_other tac :=
  let run := ltac2:(tac |- zesu_failure_memo_ltac1 "zesu_test_memo_other" tac) in
  run tac.

Lemma failure_memo_same_goal (x y : Z) : 0 <= y -> x < 5 -> x + 1 < 7.
Proof.
  intros Hy Hx.
  Fail zesu_test_memo ltac:(fail).
  (* The same site, goal and context fail at once. *)
  Fail zesu_test_memo ltac:(lia).
  (* Another site is not affected. *)
  zesu_test_memo_other ltac:(idtac).
  (* A changed context is a new key. *)
  clear Hy.
  zesu_test_memo ltac:(lia).
Qed.

(* A changed conclusion is a new key. *)
Lemma failure_memo_other_goal (x : Z) : x < 5 -> x < 6 /\ x < 7.
Proof.
  intros Hx. split.
  - Fail zesu_test_memo ltac:(fail).
    Fail zesu_test_memo ltac:(lia).
    lia.
  - zesu_test_memo ltac:(lia).
Qed.

(* Only failures are recorded: a site that succeeded and then failed after
   backtracking into it records nothing. *)
Lemma failure_memo_failure_after_success (x : Z) : x < 5 -> x < 6.
Proof.
  intros Hx.
  Fail (zesu_test_memo ltac:(idtac + idtac); fail).
  zesu_test_memo ltac:(lia).
Qed.

(* The memo belongs to one proof: a failure recorded in one proof does not
   refuse the same goal and context in the next proof. *)
Lemma failure_memo_recorded (x : Z) : x < 5 -> x < 6.
Proof.
  intros Hx.
  Fail zesu_test_memo ltac:(fail).
  Fail zesu_test_memo ltac:(lia).
  lia.
Qed.

Lemma failure_memo_new_proof (x : Z) : x < 5 -> x < 6.
Proof.
  intros Hx.
  zesu_test_memo ltac:(lia).
Qed.

(* A goal with an undefined evar has no key and always runs. *)
Lemma failure_memo_evar_goal : exists n : Z, n < 5.
Proof.
  eexists.
  Fail zesu_test_memo ltac:(fail).
  zesu_test_memo ltac:(instantiate (1 := 0); lia).
Qed.

(* A failure keeps its level: `fail 1` still escapes the enclosing `first`. *)
Goal True.
Proof.
  Fail first [zesu_test_memo ltac:(fail 1) | exact I].
  first [zesu_test_memo_other ltac:(fail 0) | exact I].
Qed.

(* The project solvers go through the memo: a failure in a smaller context
   does not refuse the same goal once the context has the needed fact. *)
Lemma failure_memo_project_lia (x y : Z) : 0 <= x -> x < y -> 0 < y.
Proof.
  intros Hx Hxy.
  Fail (clear Hxy; lia).
  Fail (clear Hxy; lia).
  Fail (clear Hxy; bv_solve).
  lia.
Qed.
