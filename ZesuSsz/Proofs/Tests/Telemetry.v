From Coq Require Import ZArith.ZArith.
From Ltac2 Require Import Ltac2.
Require Import ZesuSsz.Automation2.Telemetry.
Require Import ZesuSsz.Automation2.All.
Set Default Proof Mode "Classic".
Local Open Scope Z_scope.

(* Telemetry wrappers (Telemetry.v) never change a tactic's result: both the
   switch path and the measuring path keep successes, backtracking and
   failures. The measuring path runs here whatever ZESU_TELEMETRY says. *)
Ltac zesu_test_measured tac :=
  let run := ltac2:(tac |- zesu_telemetry_measure "test" "zesu_test_measured"
    (fun () => Ltac1.run tac)) in
  run tac.
Ltac zesu_test_switched tac :=
  let run := ltac2:(tac |- zesu_telemetry_ltac1 "test" "zesu_test_switched" tac) in
  run tac.
Ltac zesu_test_staged tac :=
  let run := ltac2:(tac |- zesu_telemetry_stage_ltac1 "zesu_test_staged" tac) in
  run tac.

(* A later failure backtracks into the second success. *)
Lemma telemetry_measured_backtracks : exists n : nat, n = 1%nat.
Proof.
  zesu_test_measured ltac:(multimatch constr:(true) with
    | _ => exists 0%nat | _ => exists 1%nat end); reflexivity.
Qed.

Lemma telemetry_switched_backtracks : exists n : nat, n = 1%nat.
Proof.
  zesu_test_switched ltac:(multimatch constr:(true) with
    | _ => exists 0%nat | _ => exists 1%nat end); reflexivity.
Qed.

Lemma telemetry_staged_backtracks : exists n : nat, n = 1%nat.
Proof.
  zesu_test_staged ltac:(multimatch constr:(true) with
    | _ => exists 0%nat | _ => exists 1%nat end); reflexivity.
Qed.

(* A failure keeps its level: `fail 1` still escapes the enclosing `first`. *)
Goal True.
Proof.
  Fail first [zesu_test_measured ltac:(fail 1) | exact I].
  Fail first [zesu_test_switched ltac:(fail 1) | exact I].
  first [zesu_test_measured ltac:(fail 0) | exact I].
Qed.

(* The project solvers still close through the wrappers. *)
Lemma telemetry_lia (x y : Z) : 0 <= x -> x < y -> 0 < y.
Proof. intros. zesu_test_measured ltac:(lia). Qed.
