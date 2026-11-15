From Coq Require Import Lists.List ZArith.ZArith.
Require Import isla.riscv64.riscv64.
Import ListNotations.
Require Import ZesuSsz.Automation2.All.
Local Open Scope Z_scope.

(* A whole 40-byte array (a callee's output) at the start of a 256-byte
   uninitialized request: the array weakens at its literal length, and the
   rest of the request meets the uninitialized region after it. The 8-byte
   rule used to commit here and leave `length bytes = 8`. *)
Lemma test_byte_array_40_uninit_subsumption `{!islaG Sigma}
    (base : Z) (bytes : list (bv 8)) :
  length bytes = 40%nat ->
  0 <= base ->
  base + 256 < 2 ^ 64 ->
  (base + 40) ↦ₘ? 216 -∗
  subsume (base ↦ₘ∗ bytes) (fun _ : unit => base ↦ₘ? 256)
    (fun _ => True%I).
Proof.
  intros Hlength Hbase Hbound. iStartProof. liARun.
  Unshelve. all: prepare_sidecond; try assumption; try lia.
Qed.

Print Assumptions test_byte_array_40_uninit_subsumption.

(* The length comes from a stated equation or from a list that computes;
   an unknown length gives no instance. *)
Lemma test_byte_array_known_length_guard (bytes : list (bv 8)) :
  length bytes = 40%nat -> True.
Proof.
  intros Hlength.
  let _ := constr:(_ : ZesuSsz.Automation2.ByteArrays.ZesuByteArrayKnownLength bytes 40) in idtac.
  clear Hlength.
  Fail let _ := constr:(_ : ZesuSsz.Automation2.ByteArrays.ZesuByteArrayKnownLength bytes _) in idtac.
  let _ := constr:(_ : ZesuSsz.Automation2.ByteArrays.ZesuByteArrayKnownLength
    [0%bv; 1%bv; 2%bv] 3) in idtac.
  exact I.
Qed.
