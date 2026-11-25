From Coq Require Import ZArith.
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Automation2.All.
Open Scope Z_scope.

(* The sample-root evaluation computes only an expression closed but for its
   root; an expression with another open atom is refused before the VM runs
   (on txAccessList 0204 the VM normalised such an address to 18 GB). *)
Lemma sample_eval_closed_but_root (root : bv 64) : True.
Proof.
  let d := ZesuSsz.Automation2.WrappedWord.zesu_eval_at_root root
    constr:(bv_unsigned (root + BV 64 8)) in
  lazymatch d with 2952790024 => idtac end.
  exact I.
Qed.

Lemma sample_eval_refuses_open (root other : bv 64) : True.
Proof.
  Fail let d := ZesuSsz.Automation2.WrappedWord.zesu_eval_at_root root
    constr:(bv_unsigned (root + (other ≪ BV 64 5))) in idtac.
  pose (shifted := (other ≪ BV 64 5)%bv).
  Fail let d := ZesuSsz.Automation2.WrappedWord.zesu_eval_at_root root
    constr:(bv_unsigned (root + shifted)) in idtac.
  exact I.
Qed.
