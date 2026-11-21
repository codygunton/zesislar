From Coq Require Import Lists.List ZArith.ZArith NArith.NArith.
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Automation2.All.
Local Open Scope Z_scope.

(* StoreMemoryLookup.zesu_run_list_eq, the last step of the explicit frame
   fold (decodeParentHeader 0570, 04b0): the folded run is an 8-byte word
   loaded from a list `l` at a start spelled by a stack offset chain (a local
   definition, as the block's trace binds it) and a flag byte; the request
   spells the word by the byte positions `nth k l`. The equation is open, so
   it is never evaluated (`vm_compute` of the old step on the 0570 goal grew
   past 24 GiB): the cells become byte extracts, the start a literal and the
   window byte positions. *)
Notation w0 l := (bv_concat 64 (bv_concat 56 (bv_concat 48 (bv_concat 40 (bv_concat 32 (bv_concat 24
     (bv_concat 16 (nth 7 l (BV 8 0)) (nth 6 l (BV 8 0))) (nth 5 l (BV 8 0)))
     (nth 4 l (BV 8 0))) (nth 3 l (BV 8 0))) (nth 2 l (BV 8 0))) (nth 1 l (BV 8 0))) (nth 0 l (BV 8 0)))
  (only parsing).

Lemma test_run_list_eq_open (sp : bv 64) (l : list (bv 8))
    (Hsp : 2684354560 + 912 <= bv_unsigned sp < 3221225472) :
  let LET0 := Z_to_bv 64 (little_endian_to_bv 8 (take (N.to_nat 8) (drop
     (Z.to_nat (bv_unsigned (sp + BV 64 18446744073709551216 + BV 64 400 + BV 64 18446744073709551432) -
                (bv_unsigned sp - 400 + 48 + 56 + 40 + 16 + 56))) l))) in
  let LET1 := bv_extract 0 8 (BV 64 1) in
  bv_to_little_endian (N.to_nat 8) 8 (bv_unsigned LET0) ++
    bv_to_little_endian (N.to_nat 1) 8 (bv_unsigned LET1) =
  [bv_extract 0 8 (w0 l); bv_extract 8 8 (w0 l); bv_extract 16 8 (w0 l); bv_extract 24 8 (w0 l);
   bv_extract 32 8 (w0 l); bv_extract 40 8 (w0 l); bv_extract 48 8 (w0 l); bv_extract 56 8 (w0 l);
   BV 8 1].
Proof.
  intros LET0 LET1.
  (* The guard: the equation is open, so the evaluation branch is refused. *)
  lazymatch goal with |- ?g =>
    assert_fails (ZesuSsz.Automation2.VmClosed.zesu_vm_closed g) end.
  ZesuSsz.Automation2.StoreMemoryLookup.zesu_run_list_eq.
Qed.

(* Closed bytes are still decided by computation. *)
Lemma test_run_list_eq_closed :
  bv_to_little_endian (N.to_nat 8) 8 (bv_unsigned (BV 64 258)) ++
    bv_to_little_endian (N.to_nat 1) 8 (bv_unsigned (BV 8 7)) =
  [BV 8 2; BV 8 1; BV 8 0; BV 8 0; BV 8 0; BV 8 0; BV 8 0; BV 8 0; BV 8 7].
Proof.
  lazymatch goal with |- ?g => ZesuSsz.Automation2.VmClosed.zesu_vm_closed g end.
  ZesuSsz.Automation2.StoreMemoryLookup.zesu_run_list_eq.
Qed.

(* Refused: a byte that is another position of the list. *)
Lemma test_run_list_eq_open_other (l : list (bv 8)) :
  let LET0 := Z_to_bv 64 (little_endian_to_bv 8 (take 8 (drop 0 l))) in
  bv_to_little_endian (N.to_nat 8) 8 (bv_unsigned LET0) =
  [nth 1 l (BV 8 0); bv_extract 8 8 (w0 l); bv_extract 16 8 (w0 l); bv_extract 24 8 (w0 l);
   bv_extract 32 8 (w0 l); bv_extract 40 8 (w0 l); bv_extract 48 8 (w0 l); bv_extract 56 8 (w0 l)] ->
  True.
Proof.
  intros LET0 _.
  assert_fails (assert (bv_to_little_endian (N.to_nat 8) 8 (bv_unsigned LET0) =
    [nth 1 l (BV 8 0); bv_extract 8 8 (w0 l); bv_extract 16 8 (w0 l); bv_extract 24 8 (w0 l);
     bv_extract 32 8 (w0 l); bv_extract 40 8 (w0 l); bv_extract 48 8 (w0 l); bv_extract 56 8 (w0 l)])
    by ZesuSsz.Automation2.StoreMemoryLookup.zesu_run_list_eq).
  exact I.
Qed.
