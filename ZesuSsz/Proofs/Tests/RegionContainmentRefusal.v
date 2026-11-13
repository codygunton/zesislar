From Coq Require Import ZArith.ZArith.
From stdpp.bitvector Require Import definitions.
Require Import ZesuSsz.Automation2.All.
Local Open Scope Z_scope.

(* The refusal checks below are `Fail` checks; this one makes sure the
   class they ask for exists, so they cannot pass for a missing name. *)
Check ZesuSsz.Automation2.UninitRegions.ZesuRegionNotRefuted.

(* The fallback rule for an uninitialized region refuses a containment
   that the facts already refute, and still applies when they do not. *)
Lemma region_refusal_false_containment (a : Z) : True.
Proof.
  Fail let _ := constr:(_ : ZesuSsz.Automation2.UninitRegions.ZesuRegionNotRefuted
    (0 <= 64 /\ a <= a /\ a + 64 <= a + 48)) in idtac.
  exact I.
Qed.

Lemma region_refusal_false_containment_from_facts (a n1 : Z) : n1 = 48 -> True.
Proof.
  intros Hsize.
  Fail let _ := constr:(_ : ZesuSsz.Automation2.UninitRegions.ZesuRegionNotRefuted
    (0 <= 64 /\ a <= a /\ a + 64 <= a + n1)) in idtac.
  exact I.
Qed.

(* A region size that only bitvector arithmetic reduces: 48 bytes. *)
Lemma region_refusal_false_containment_bv (f : Z) : 64 <= f < 2 ^ 64 -> True.
Proof.
  intros Hf.
  Fail let _ := constr:(_ : ZesuSsz.Automation2.UninitRegions.ZesuRegionNotRefuted
    (0 <= 64 /\ f - 64 <= f - 64 /\
     f - 64 + 64 <= f - 64 +
       (bv_unsigned (Z_to_bv 64 f - Z_to_bv 64 64 + Z_to_bv 64 48) - (f - 64)))) in idtac.
  exact I.
Qed.

Lemma region_refusal_keeps_true_containment (a : Z) : True.
Proof.
  let _ := constr:(_ : ZesuSsz.Automation2.UninitRegions.ZesuRegionNotRefuted
    (0 <= 16 /\ a <= a /\ a + 16 <= a + 48)) in idtac.
  exact I.
Qed.

(* Unknown sizes are not refuted: the obligation stays for later facts. *)
Lemma region_refusal_keeps_unknown_containment (a n1 n2 : Z) : True.
Proof.
  let _ := constr:(_ : ZesuSsz.Automation2.UninitRegions.ZesuRegionNotRefuted
    (0 <= n2 /\ a <= a /\ a + n2 <= a + n1)) in idtac.
  exact I.
Qed.
