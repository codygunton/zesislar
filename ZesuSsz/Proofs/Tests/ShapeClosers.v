From Coq Require Import ZArith.ZArith Lists.List NArith.NArith.
From stdpp.bitvector Require Import definitions.
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Automation2.All.
Local Open Scope Z_scope.

(* The finisher's shape closers: pure goals of a known shape, closed from the
   facts on the goal's own terms before the context-wide solvers run. Each
   test goes through the dispatcher, so it fails when its closer is missing
   from it. *)

(* One bit of a word, from a fact that masks the word with that bit alone. *)
Goal forall (status : bv 64), bv_and status (BV 64 131072) = 0%bv ->
  bv_extract 17 1 status <> BV 1 1.
Proof. intros status Hmask. ZesuSsz.Automation2.Finish.zesu_finish_shape_closers. Qed.

Goal forall (status : bv 64), bv_and status (BV 64 131072) = 0%bv ->
  bv_unsigned (bv_extract 17 1 status) <> 1.
Proof. intros status Hmask. ZesuSsz.Automation2.Finish.zesu_finish_shape_closers. Qed.

Goal forall (status : bv 64), Z.land (bv_unsigned status) 131072 = 0 ->
  bv_extract 17 1 status = BV 1 0.
Proof. intros status Hmask. ZesuSsz.Automation2.Finish.zesu_finish_shape_closers. Qed.

(* A mask of another bit says nothing about this one: refused. *)
Goal forall (status : bv 64), bv_and status (BV 64 65536) = 0%bv ->
  bv_extract 17 1 status <> BV 1 1 -> True.
Proof.
  intros status Hmask. Fail ZesuSsz.Automation2.Finish.zesu_finish_shape_closers.
  intros _. exact I.
Qed.

(* A window of a list against the list's byte positions. *)
Goal forall (bytes : list (bv 8)),
  bv_zero_extend 64 (Z_to_bv 16 (little_endian_to_bv 8 (take (N.to_nat 2) (drop 32 bytes)))) =
  bv_zero_extend 64 (bv_concat 16 (nth 33 bytes (BV 8 0)) (nth 32 bytes (BV 8 0))).
Proof. intros bytes. ZesuSsz.Automation2.Finish.zesu_finish_shape_closers. Qed.

(* The window holds other bytes than the positions: refused. *)
Goal forall (bytes : list (bv 8)),
  bv_zero_extend 64 (Z_to_bv 16 (little_endian_to_bv 8 (take (N.to_nat 2) (drop 32 bytes)))) =
  bv_zero_extend 64 (bv_concat 16 (nth 34 bytes (BV 8 0)) (nth 33 bytes (BV 8 0))) -> True.
Proof.
  intros bytes. Fail ZesuSsz.Automation2.Finish.zesu_finish_shape_closers.
  intros _. exact I.
Qed.

(* The bv_unsigned view of a branch fact on the goal's word. *)
Goal forall (high low : bv 8),
  bv_zero_extend 64 (bv_concat 16 high low) = BV 64 0 ->
  bv_unsigned (bv_concat 16 high low) = 0.
Proof. intros high low Hbranch. ZesuSsz.Automation2.Finish.zesu_finish_shape_closers. Qed.

Goal forall (high low : bv 8),
  bv_zero_extend 64 (bv_concat 16 high low) <> BV 64 0 ->
  bv_unsigned (bv_concat 16 high low) <> 0.
Proof. intros high low Hbranch. ZesuSsz.Automation2.Finish.zesu_finish_shape_closers. Qed.

(* A branch fact on another word: refused. *)
Goal forall (high low : bv 8),
  bv_zero_extend 64 (bv_concat 16 low high) = BV 64 0 ->
  bv_unsigned (bv_concat 16 high low) = 0 -> True.
Proof.
  intros high low Hbranch. Fail ZesuSsz.Automation2.Finish.zesu_finish_shape_closers.
  intros _. exact I.
Qed.

(* An array bound on an index measured from a closed-offset chain on a
   word, against a list of known length. *)
Record ShapeFrame := { shapePointer : bv 64 }.
Definition shapeFrameWellFormed (frame : ShapeFrame) : Prop :=
  (4096 <= bv_unsigned (shapePointer frame))%Z /\
  (bv_unsigned (shapePointer frame) < 4294967296)%Z.

Goal forall frame (bytes : list (bv 8)), shapeFrameWellFormed frame ->
  length bytes = 40%nat ->
  (Z.to_nat (bv_unsigned (shapePointer frame + BV 64 18446744073709551216 +
    BV 64 400 + BV 64 18446744073709551256) -
    (bv_unsigned (shapePointer frame) - 400 + 8)) + N.to_nat 2 <= length bytes)%nat.
Proof.
  intros frame bytes Hframe Hlength.
  ZesuSsz.Automation2.Finish.zesu_finish_shape_closers.
Qed.

(* The same index past the end of a shorter list: refused. *)
Goal forall frame (bytes : list (bv 8)), shapeFrameWellFormed frame ->
  length bytes = 33%nat ->
  (Z.to_nat (bv_unsigned (shapePointer frame + BV 64 18446744073709551216 +
    BV 64 400 + BV 64 18446744073709551256) -
    (bv_unsigned (shapePointer frame) - 400 + 8)) + N.to_nat 2 <= length bytes)%nat -> True.
Proof.
  intros frame bytes Hframe Hlength.
  Fail ZesuSsz.Automation2.Finish.zesu_finish_shape_closers.
  intros _. exact I.
Qed.
