(* Tests for the closedness check before VM evaluation: it agrees with stdpp
   `is_closed_term` on closed and open terms, and its cost does not grow with
   the square of the context size. *)
From Coq Require Import ZArith NArith.
From stdpp Require Import tactics bitvector.definitions.
Require Import ZesuSsz.Automation2.All.

(* Both checks accept, or both refuse. *)
Ltac vm_closed_term_agrees term :=
  tryif stdpp.tactics.is_closed_term term then
    ZesuSsz.Automation2.VmClosed.zesu_closed_term term
  else
    tryif ZesuSsz.Automation2.VmClosed.zesu_closed_term term then fail
    else idtac.

Ltac vm_closed_term_accepts term :=
  stdpp.tactics.is_closed_term term;
  ZesuSsz.Automation2.VmClosed.zesu_closed_term term.

Ltac vm_closed_term_refuses term :=
  tryif stdpp.tactics.is_closed_term term then fail else idtac;
  tryif ZesuSsz.Automation2.VmClosed.zesu_closed_term term then fail else idtac.

Lemma vm_closed_term_corpus (x : Z) (n : nat) (word : bv 64) (Hx : (0 <= x)%Z) : True.
Proof.
  set (literal := 3%Z).
  set (sum := (literal + 4)%Z).
  set (open := (x + 1)%Z).
  set (product := (sum * open)%Z).
  set (closedWord := bv_add (BV 64 3) (Z_to_bv 64 sum)).
  assert (Hcopy : x = x) by reflexivity.
  set (twice := (sum + sum)%Z).
  (* Closed literals and closed local definitions. *)
  vm_closed_term_accepts (1 + 2)%Z.
  vm_closed_term_accepts literal.
  vm_closed_term_accepts sum.
  vm_closed_term_accepts (sum + twice)%Z.
  vm_closed_term_accepts closedWord.
  vm_closed_term_accepts (bv_unsigned closedWord <= 2 ^ 64)%Z.
  vm_closed_term_accepts (Z.to_nat (bv_unsigned (Z_to_bv 64 7)) < 8)%nat.
  vm_closed_term_accepts (fun z : Z => z + literal)%Z.
  vm_closed_term_accepts (forall z : Z, z = twice).
  vm_closed_term_accepts (bool_decide (sum <= twice)%Z).
  (* Symbolic terms, direct or through a local definition. *)
  vm_closed_term_refuses x.
  vm_closed_term_refuses (x + 0)%Z.
  vm_closed_term_refuses open.
  vm_closed_term_refuses product.
  vm_closed_term_refuses (product + literal)%Z.
  vm_closed_term_refuses (fun z : Z => z + x)%Z.
  vm_closed_term_refuses Hcopy.
  vm_closed_term_refuses Hx.
  vm_closed_term_refuses (Z.of_nat n).
  vm_closed_term_refuses (bv_add word closedWord).
  vm_closed_term_refuses (forall z : Z, z = open).
  vm_closed_term_agrees (sum = twice).
  vm_closed_term_agrees (open = twice).
  exact I.
Qed.

(* Terms with evars: an evar keeps its whole context through `clear -`, so
   the check falls back to the stdpp loop and agrees with it. *)
Lemma vm_closed_term_evars (x : Z) : True.
Proof.
  set (literal := 3%Z).
  evar (value : Z).
  set (closedAlias := (value + literal)%Z).
  evar (proof : x = x).
  set (openAlias := (x + value)%Z).
  vm_closed_term_accepts value.
  vm_closed_term_accepts closedAlias.
  vm_closed_term_accepts (value + 1)%Z.
  vm_closed_term_refuses openAlias.
  vm_closed_term_refuses (value + x)%Z.
  vm_closed_term_refuses proof.
  instantiate (value := 0%Z).
  instantiate (proof := eq_refl).
  exact I.
Qed.

(* The VM gate refuses a definition that hides an evar. *)
Lemma vm_closed_term_evar_alias : True.
Proof.
  evar (value : Z).
  pose (alias := value).
  tryif ZesuSsz.Automation2.VmClosed.zesu_vm_closed alias then fail else idtac.
  instantiate (value := 0%Z).
  ZesuSsz.Automation2.VmClosed.zesu_vm_closed alias.
  exact I.
Qed.

(* Many local definitions and hypotheses. stdpp `is_closed_term` unfolds every
   definition into every hypothesis per call; this check keeps only what the
   goal needs. The 40 calls below take well under a second. *)
Ltac vm_closed_term_context count :=
  lazymatch count with
  | O => idtac
  | S ?rest =>
      let value := fresh "value" in
      set (value := (Z.of_nat count + 1)%Z);
      let fact := fresh "fact" in
      assert (fact : value = value) by reflexivity;
      vm_closed_term_context rest
  end.

Lemma vm_closed_term_large_context (x : Z) : True.
Proof.
  vm_closed_term_context 200%nat.
  do 20 (ZesuSsz.Automation2.VmClosed.zesu_vm_closed (value + value0)%Z).
  do 20 (tryif ZesuSsz.Automation2.VmClosed.zesu_vm_closed (value + x)%Z
    then fail else idtac).
  exact I.
Qed.
