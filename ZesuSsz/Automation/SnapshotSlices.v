Require Import ZesuSsz.Automation.All.
Require Import isla.riscv64.riscv64.
From Coq Require Import ZArith.ZArith.
Lemma snapshot_memory_slice (memory : mem_map) (base : Z)
    (bytes : list byte) (start count : nat) :
  (start + count <= length bytes)%nat ->
  read_mem_list memory base (N.of_nat (length bytes)) = Some bytes ->
  read_mem_list memory (base + Z.of_nat start)%Z (N.of_nat count) =
    Some (take count (drop start bytes)).
Proof.
  intros Hbound Hread. unfold read_mem_list in *.
  rewrite !nat_N_Z in Hread. rewrite !nat_N_Z.
  apply mapM_Some_1 in Hread.
  have HboundZ : (Z.of_nat start + Z.of_nat count <= Z.of_nat (length bytes))%Z.
  { apply Nat2Z.inj_le in Hbound. rewrite Nat2Z.inj_add in Hbound. exact Hbound. }
  have Hsplit : seqZ base (Z.of_nat (length bytes)) =
    seqZ base (Z.of_nat start) ++
    (seqZ (base + Z.of_nat start) (Z.of_nat count) ++
      seqZ (base + Z.of_nat start + Z.of_nat count)
        (Z.of_nat (length bytes) - Z.of_nat start - Z.of_nat count)).
  { replace (Z.of_nat (length bytes)) with
      (Z.of_nat start + (Z.of_nat count +
        (Z.of_nat (length bytes) - Z.of_nat start - Z.of_nat count)))%Z at 1 by lia.
    rewrite (seqZ_app base (Z.of_nat start)
      (Z.of_nat count + (Z.of_nat (length bytes) - Z.of_nat start - Z.of_nat count))
      ltac:(lia) ltac:(lia)).
    rewrite (seqZ_app (base + Z.of_nat start) (Z.of_nat count)
      (Z.of_nat (length bytes) - Z.of_nat start - Z.of_nat count)
      ltac:(lia) ltac:(lia)). reflexivity. }
  have Hslice := Forall2_take _ _ _ count (Forall2_drop _ _ _ start Hread).
  rewrite Hsplit in Hslice.
  rewrite (drop_app_length' _ _ start) in Hslice.
  2: rewrite length_seqZ Nat2Z.id; reflexivity.
  rewrite (take_app_length' _ _ count) in Hslice.
  2: rewrite length_seqZ Nat2Z.id; reflexivity.
  apply mapM_Some_2. exact Hslice.
Qed.
Print Assumptions snapshot_memory_slice.
