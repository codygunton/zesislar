Require Import ZesuSsz.Automation.AllLegacy.
Require Import ZesuSsz.Automation.SnapshotSlices.
Require Import isla.riscv64.riscv64.

Lemma test_snapshot_address_payload memory base (bytes : list byte) :
  length bytes = 40%nat ->
  read_mem_list memory base (N.of_nat (length bytes)) = Some bytes ->
  read_mem_list memory (base + 16)%Z 20 = Some (take 20 (drop 16 bytes)).
Proof.
  intros Hlen Hread.
  apply (snapshot_memory_slice memory base bytes 16 20); [lia|exact Hread].
Qed.
Print Assumptions test_snapshot_address_payload.
