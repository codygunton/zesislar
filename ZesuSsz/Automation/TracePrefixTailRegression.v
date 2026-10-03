Require Import ZesuSsz.Automation.All.
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Export.Snapshots.
Require Import ZesuSsz.Automation.TracePrefixTail.

Lemma event_address_equal (entrysp frameSp : bv 64) (tail : spec) :
  (2048 <= bv_unsigned entrysp)%Z ->
  frameSp = (entrysp - 2000)%bv ->
  scons (SWriteMem (BV 64 604086456) (entrysp - (2000 + 48))%bv) tail ⊆
  scons (SWriteMem (BV 64 604086456) (frameSp - 48)%bv) tail.
Proof. intros Hlow Hframe. zesu_trace_prefix_inclusion. Qed.
Print Assumptions event_address_equal.

Lemma event_snapshot_address_equal (entrysp frameSp : bv 64)
 (accept : seq_snapshot -> Prop) (tail : spec) :
 (2048 <= bv_unsigned entrysp)%Z ->
  frameSp = (entrysp - 2000)%bv ->
 scons_snap (SWriteMem (BV 64 604086456) (entrysp - (2000 + 48))%bv) accept tail ⊆
 scons_snap (SWriteMem (BV 64 604086456) (frameSp - 48)%bv) accept tail.
Proof. intros Hlow Hframe. zesu_trace_prefix_inclusion. Qed.
Print Assumptions event_snapshot_address_equal.

Goal True.
Proof.
 Fail assert (scons (SWriteMem (BV 64 604086456) (BV 64 8))
   (fun _ => False) ⊆ scons (SWriteMem (BV 64 604086456) (BV 64 16))
   (fun _ => False)) by zesu_trace_prefix_inclusion.
 exact I.
Qed.

Goal True.
Proof.
 Fail assert (scons_snap (SWriteMem (BV 64 604086456) (BV 64 8))
   (fun _ => True) (fun _ => False) ⊆
   scons_snap (SWriteMem (BV 64 604086456) (BV 64 8))
   (fun _ => False) (fun _ => False)) by zesu_trace_prefix_inclusion.
 exact I.
Qed.

Lemma output_prefix_address_equal (entrysp frameSp : bv 64)
 (payload : list (bv 8)) (tail : spec) :
 (2048 <= bv_unsigned entrysp)%Z ->
 frameSp = (entrysp - 2000)%bv ->
 writeOutputEvents (entrysp - (2000 + 48))%bv (BV 64 32) payload tail ⊆
 writeOutputEvents (frameSp - 48)%bv (BV 64 32) payload tail.
Proof. intros Hlow Hframe. zesu_trace_prefix_inclusion. Qed.
Print Assumptions output_prefix_address_equal.

Goal True.
Proof.
 Fail assert (scons (SWriteMem (BV 64 604086456) (BV 64 8))
   (scons (SWriteMem (BV 64 604086464) (BV 64 16)) (fun _ => False)) ⊆
   scons (SWriteMem (BV 64 604086456) (BV 64 8))
   (scons (SWriteMem (BV 64 604086464) (BV 64 32)) (fun _ => False)))
   by zesu_trace_prefix_inclusion.
 exact I.
Qed.
