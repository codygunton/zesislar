From Coq Require Import ZArith.ZArith.
From Ltac2 Require Import Ltac2.
Require Import ZesuSsz.Automation2.Telemetry.
Require Import ZesuSsz.Automation2.LinearFirstLia.
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

(* `zesu_telemetry_sizes` counts the Prop facts without a body, their nodes
   and the goal's nodes in the units of LinearFirstLia's budget walk. *)
Ltac2 zesu_test_walk (term : constr) : int :=
  Int.sub 1000000 (zesu_linear_remaining 1000000 term).

Ltac2 zesu_test_sizes_match () :=
  let facts := List.filter (fun declaration =>
    let (_, body, typ) := declaration in
    match body with
    | None => zesu_linear_is_prop typ
    | Some _ => false
    end) (Control.hyps ()) in
  let nodes := List.fold_left (fun sum declaration =>
    let (_, _, typ) := declaration in Int.add sum (zesu_test_walk typ)) 0 facts in
  let expected := [List.length facts; nodes; zesu_test_walk (Control.goal ())] in
  let sizes := zesu_telemetry_sizes () in
  let differ () := Control.throw (Tactic_failure (Some (Message.of_string "telemetry sizes differ"))) in
  if Int.equal (List.length sizes) 3
  then (if List.for_all2 Int.equal sizes expected then () else differ ())
  else differ ().

Lemma telemetry_sizes_walk (x y : Z) (b : bool) (f : Z -> Z) :
  0 <= x -> x < f y + 1 -> b = true -> (forall z, f z = z) -> 0 < f y + 1.
Proof.
  intros Hx Hy Hb Hf. set (w := x + 1).
  ltac2:(zesu_test_sizes_match ()).
  rewrite Hf in *. lia.
Qed.

(* Step and alternative records (`zesu_tstep`, `zesu_talt`): the measuring
   paths and the switched notations keep successes, backtracking and
   failures. *)
Ltac zesu_test_alt_measured tac :=
  let run := ltac2:(tac |- zesu_telemetry_alt_measured "zesu_test_alt" tac) in
  run tac.
Ltac zesu_test_step_measured tac :=
  let run := ltac2:(tac |- zesu_telemetry_step_measured tac) in
  run tac.

Lemma telemetry_alt_backtracks : exists n : nat, n = 1%nat.
Proof.
  zesu_test_alt_measured ltac:(multimatch constr:(true) with
    | _ => exists 0%nat | _ => exists 1%nat end); reflexivity.
Qed.

Lemma telemetry_step_backtracks : exists n : nat, n = 1%nat.
Proof.
  zesu_test_step_measured ltac:(multimatch constr:(true) with
    | _ => exists 0%nat | _ => exists 1%nat end); reflexivity.
Qed.

Lemma telemetry_talt_backtracks : exists n : nat, n = 1%nat.
Proof.
  zesu_tstep (zesu_talt zesu_test_alt (idtac; multimatch constr:(true) with
    | _ => exists 0%nat | _ => exists 1%nat end)); reflexivity.
Qed.

Goal True.
Proof.
  Fail first [zesu_test_alt_measured ltac:(fail 1) | exact I].
  Fail first [zesu_test_step_measured ltac:(fail 1) | exact I].
  Fail first [zesu_talt zesu_test_alt (idtac; fail 1) | exact I].
  Fail first [zesu_tstep (fail 1) | exact I].
  first [zesu_talt zesu_test_alt (idtac; fail 0) | exact I].
Qed.

(* A search loop through both wrappers ends where the bare loop ends. *)
Lemma telemetry_step_loop : True /\ True /\ True.
Proof.
  repeat (zesu_tstep (first [zesu_talt zesu_test_split (idtac; split) |
    zesu_talt zesu_test_exact (idtac; exact I)])).
Qed.

(* With several goals focused the step record names no goal and still runs. *)
Lemma telemetry_step_unfocused : True /\ True.
Proof.
  split.
  all: zesu_test_step_measured ltac:(exact I).
Qed.

(* A later failure backtracks through an alternative and a step that
   succeeded once: the failure goes on to the next branch unchanged. With
   ZESU_TELEMETRY=1 the measured alternative prints kind=alt for its own
   time and kind=backtrack for the failing continuation, never altfail. *)
Ltac zesu_test_slow_failure := do 20000 idtac; fail.

Lemma telemetry_alt_backtrack_through : True.
Proof.
  first [zesu_test_alt_measured ltac:(idtac); zesu_test_slow_failure | exact I].
Qed.

Lemma telemetry_step_backtrack_through : True.
Proof.
  first [zesu_test_step_measured ltac:(idtac); zesu_test_slow_failure | exact I].
Qed.

Lemma telemetry_talt_backtrack_through : True.
Proof.
  first [zesu_tstep (zesu_talt zesu_test_gate (idtac; idtac)); zesu_test_slow_failure | exact I].
Qed.
