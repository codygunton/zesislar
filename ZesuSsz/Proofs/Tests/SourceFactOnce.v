From Coq Require Import ZArith.ZArith.
From stdpp.bitvector Require Import definitions.
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Automation2.All.
From Ltac2 Require Import Ltac2 Ref.
Set Default Proof Mode "Classic".
Local Open Scope Z_scope.

(* `SourceFactMatching.zesu_source_fact_once` proves a fact without an open evar
   once. Each fact below has two retained order hypotheses, so the closers
   prove it in two ways; a failure after k such facts retried 2^k
   combinations (decodeParentHeader 046c: the deferring route ran 1,024
   rounds). Counted here: the successes of the fixed-fact walks over three
   facts, 1 each (8 before). *)

Ltac2 count_successes (t : unit -> unit) : int :=
  let c := Ref.ref 0 in
  Control.plus
    (fun () => t (); Ref.set c (Int.add (Ref.get c) 1); Control.zero (Tactic_failure None))
    (fun _ => ());
  Ref.get c.

Ltac2 expect_successes (n : int) (t : unit -> unit) :=
  let found := count_successes t in
  if Int.equal found n then ()
  else Control.throw (Tactic_failure (Some (Message.concat
    (Message.of_string "successes: ") (Message.of_int found)))).

Lemma source_fact_once_fixed `{!islaG Σ} (a b c d e f : bv 64) :
  ~ (bv_signed (bv_zero_extend 128 a) < bv_signed (bv_zero_extend 128 b)) ->
  ~ (bv_signed (bv_zero_extend 128 a) < bv_signed (bv_zero_extend 128 b)) ->
  ~ (bv_signed (bv_zero_extend 128 c) < bv_signed (bv_zero_extend 128 d)) ->
  ~ (bv_signed (bv_zero_extend 128 c) < bv_signed (bv_zero_extend 128 d)) ->
  ~ (bv_signed (bv_zero_extend 128 e) < bv_signed (bv_zero_extend 128 f)) ->
  ~ (bv_signed (bv_zero_extend 128 e) < bv_signed (bv_zero_extend 128 f)) ->
  True.
Proof.
  intros.
  (* One fact: the alternatives alone prove it twice, the step once. *)
  ltac2:(expect_successes 2 (fun () => ltac1:(
    assert (bv_unsigned a >= bv_unsigned b)
      by ZesuSsz.Automation2.SourceFactMatching.zesu_source_fact))).
  ltac2:(expect_successes 1 (fun () => ltac1:(
    assert (bv_unsigned a >= bv_unsigned b)
      by ZesuSsz.Automation2.SourceFactMatching.zesu_source_fact_once))).
  (* Three facts in a package: one round for the deferring walk and the
     strict walk. *)
  ltac2:(expect_successes 1 (fun () => ltac1:(
    ZesuSsz.Automation2.SourceFactMatching.zesu_source_defer_fixed_tree
      constr:((⌜bv_unsigned a >= bv_unsigned b⌝ ∗ ⌜bv_unsigned c >= bv_unsigned d⌝ ∗
               ⌜bv_unsigned e >= bv_unsigned f⌝)%I : iProp Σ)))).
  ltac2:(expect_successes 1 (fun () => ltac1:(
    ZesuSsz.Automation2.SourceFactMatching.zesu_source_check_fixed_tree
      constr:((⌜bv_unsigned a >= bv_unsigned b⌝ ∗ ⌜bv_unsigned c >= bv_unsigned d⌝ ∗
               ⌜bv_unsigned e >= bv_unsigned f⌝)%I : iProp Σ)))).
  exact I.
Qed.

(* A fact with an open evar takes the alternatives unchanged: the evar is
   chosen by them (here by the hypothesis). *)
Lemma source_fact_once_evar (a b : bv 64) :
  (bv_unsigned a <= bv_unsigned b) -> exists x : bv 64, bv_unsigned a <= bv_unsigned x.
Proof.
  intros H. eexists.
  ZesuSsz.Automation2.SourceFactMatching.zesu_source_fact_once.
Qed.

Print Assumptions source_fact_once_fixed.
Print Assumptions source_fact_once_evar.
