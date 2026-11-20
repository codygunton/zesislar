(* The occurrence test of the memory-tuple witnesses
   (ZesuSsz/Automation2/MemoryTupleConsumer.v, `zesu_memory_witness_occurs`)
   walks the requested term once. It enumerated `context [?part]`, which
   rebuilds the context of every subterm: on the open existential of a large
   successor entry (decodeParentHeader 013c, 40 unused byte witnesses and tens
   of thousands of nodes) the package step ran for minutes before it refused.
   The counts below are the nodes one test visits. *)
Require Import isla.riscv64.riscv64.
From Coq Require Import ZArith.
From stdpp Require Import bitvector.definitions.
Require Import lithium.interpreter lithium.pure_definitions.
From iris.proofmode Require Import tactics environments.
Require Import ZesuSsz.Automation2.MemoryTupleConsumer.
Require Import ZesuSsz.Automation2.All.
From Ltac2 Require Import Ltac2.
Set Default Proof Mode "Classic".

Local Open Scope Z_scope.

(* `atom /\ ... /\ atom`, `count` atoms. *)
Ltac2 rec zesu_test_conjunction (count : int) (atom : constr) : constr :=
  if Int.le count 1 then atom
  else Constr.Unsafe.make (Constr.Unsafe.App 'and [| atom; zesu_test_conjunction (Int.sub count 1) atom |]).

Ltac2 zesu_test_occurs (candidate : constr) (term : constr) (expected : bool) (visits : int) :=
  let (occurs, visited) := zesu_memory_evar_occurs_count candidate term in
  (if Bool.equal occurs expected then ()
   else Control.throw (Tactic_failure (Some (Message.of_string "wrong answer"))));
  if Int.equal visited visits then ()
  else Control.throw (Tactic_failure (Some (Message.concat (Message.of_string "visited ")
    (Message.of_int visited)))).

(* Absent: each node once. `x = x` is 5 nodes, each `/\` adds 2: 64 x 5 + 63 x 2 = 446. *)
Lemma zesu_tuple_witness_absent_walks_once (x : Z) : exists b : bv 8, b = b.
Proof.
  eexists.
  lazymatch goal with
  | |- ?b = _ =>
      let check := ltac2:(b |-
        zesu_test_occurs (Option.get (Ltac1.to_constr b))
          (zesu_test_conjunction 64 '(&x = &x)) false 446) in
      check b;
      unify b (BV 8 0)
  end.
  reflexivity.
Qed.

(* Present: the walk stops at the first occurrence, before the 63 conjuncts
   after it. *)
Lemma zesu_tuple_witness_present_stops (x : Z) : exists b : bv 8, b = b.
Proof.
  eexists.
  lazymatch goal with
  | |- ?b = _ =>
      let check := ltac2:(b |-
        let b := Option.get (Ltac1.to_constr b) in
        zesu_test_occurs b
          (Constr.Unsafe.make (Constr.Unsafe.App 'and
             [| '(&x = &x);
                Constr.Unsafe.make (Constr.Unsafe.App 'and
                  [| Constr.Unsafe.make (Constr.Unsafe.App '(@eq (bv 8)) [| b; b |]);
                     zesu_test_conjunction 63 '(&x = &x) |]) |]))
          true 23) in
      check b;
      unify b (BV 8 0)
  end.
  reflexivity.
Qed.

(* Package level, both branches. A witness the requested facts use stays open
   and is chosen by them; an unused byte-vector witness becomes zero. *)
Lemma zesu_tuple_witness_packageable (Sigma : gFunctors) (P : bv 64 -> Prop) (value : bv 64) :
  P value -> ((emp : iProp Sigma) ⊢ ∃ x : li_prod (bv 64) (li_prod (bv 64) unit), ⌜P (li_fst x)⌝)%I.
Proof.
  intros Hvalue. iIntros "_".
  ZesuSsz.Automation2.MemoryTupleConsumer.zesu_memory_open_tuple constr:(16%nat).
  iPureIntro. exact Hvalue.
Qed.

(* The leftover shape of decodeParentHeader 013c: byte witnesses that no fact
   pins, then a byte-list witness. The package step refuses it. *)
Lemma zesu_tuple_witness_open_existential_refused (Sigma : gFunctors) (P : list (bv 8) -> Prop) : True.
Proof.
  Fail (assert ((emp : iProp Sigma) ⊢ ∃ x : li_prod (bv 8) (li_prod (bv 8) (li_prod (list (bv 8)) unit)),
      ⌜P (li_fst (li_snd (li_snd x)))⌝)%I as _ by
    (iIntros "_"; ZesuSsz.Automation2.MemoryTupleConsumer.zesu_memory_open_tuple constr:(16%nat))).
  exact I.
Qed.
