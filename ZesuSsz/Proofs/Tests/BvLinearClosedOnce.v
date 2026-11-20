(* The closedness test of the reflective linear normal form
   (ZesuSsz/Automation2/BvLinear.v, `zesu_bvlin_closed`) answers once. A
   backtracking test gave a second answer (`false`) whenever a later step
   failed, so a false equation with k closed subterms was refused only after
   2^k reifications (over 100 s for one refuted memory-region candidate of a
   return block). *)
Require Import isla.riscv64.riscv64.
From Coq Require Import ZArith.
From stdpp Require Import bitvector.definitions.
Require Import ZesuSsz.Automation2.BvLinear.
Require Import ZesuSsz.Automation2.All.
From Ltac2 Require Import Ltac2.
Set Default Proof Mode "Classic".

Local Open Scope Z_scope.

(* Exactly one answer, for a closed term (true) and for an open one (false). *)
Ltac2 zesu_test_closed_once (term : constr) (expected : bool) :=
  match Control.case (fun () => zesu_bvlin_closed term) with
  | Val answer =>
      let (value, more) := answer in
      (if Bool.equal value expected then ()
       else Control.throw (Tactic_failure (Some (Message.of_string "wrong first answer"))));
      match Control.case (fun () => more Not_found) with
      | Val _ => Control.throw (Tactic_failure (Some (Message.of_string "second answer")))
      | Err _ => ()
      end
  | Err _ => Control.throw (Tactic_failure (Some (Message.of_string "no answer")))
  end.

Lemma zesu_bv_linear_closed_once_closed : True.
Proof. ltac2:(zesu_test_closed_once '(Z.of_nat 8 * 1) true). exact I. Qed.

Lemma zesu_bv_linear_closed_once_open (sp : bv 64) : True.
Proof. ltac2:(zesu_test_closed_once '(bv_unsigned &sp) false). exact I. Qed.

(* False as an equality: the left side is sp - 136, the right side sp - 128. *)
Lemma zesu_bv_linear_closed_once_refuted (sp : bv 64) :
  bv_add (bv_add (bv_add (bv_add sp (BV 64 18446744073709551216)) (BV 64 400))
    (BV 64 18446744073709551480)) (BV 64 0) <>
  Z_to_bv 64 (bv_unsigned sp - 400 + 48 + 56 + 40 + 16 + 56 + 16 + 32 + Z.of_nat 8 * 1).
Proof. zesu_bv_linear_bv. Qed.

(* The true variant still closes: closed subterms are literals. *)
Lemma zesu_bv_linear_closed_once_true (sp : bv 64) :
  bv_add (bv_add (bv_add (bv_add sp (BV 64 18446744073709551216)) (BV 64 400))
    (BV 64 18446744073709551480)) (BV 64 0) =
  Z_to_bv 64 (bv_unsigned sp - 400 + 48 + 56 + 40 + 16 + 56 + 16 + 32 + Z.of_nat 0 * 1).
Proof. zesu_bv_linear_bv. Qed.
