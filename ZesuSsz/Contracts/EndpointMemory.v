Require Import ZesuSsz.Automation.All.
From Coq Require Import ZArith.ZArith.
From stdpp Require Import gmap list_numbers.
Require Import isla.opsem.
Require Import ZesuSsz.Contracts.ElfMemory.
Require Import ZesuMachineMap.Machine.

Definition endpointInputMemory (input : list Z) : mem_map :=
  fileSegment (mapInputBufferAddress defaultMap)
    (List.map (Z_to_bv 8) input) ∪
  fileSegment (mapIoContextAddress defaultMap)
    (bv_to_little_endian 8 8 (Z.of_nat (List.length input))) ∪
  elfLoadMemory.

Lemma endpoint_input_byte input offset byte :
  (List.length input <= 64 * 1024 * 1024)%nat ->
  input !! offset = Some byte ->
  endpointInputMemory input !!
    Z_to_bv 64 (mapInputBufferAddress defaultMap + Z.of_nat offset) =
    Some (Z_to_bv 8 byte).
Proof.
  intros Hbound Hbyte.
  have Hlookup : (List.map (Z_to_bv 8) input) !! offset =
      Some (Z_to_bv 8 byte).
  { rewrite list_lookup_fmap Hbyte. reflexivity. }
  have Hkeys : NoDup (List.map (Z_to_bv 64)
      (seqZ (mapInputBufferAddress defaultMap)
        (Z.of_nat (List.length (List.map (Z_to_bv 8) input))))).
  { rewrite length_fmap. apply bounded_segment_keys_nodup;
      simpl; replace (bv_modulus 64) with 18446744073709551616
        by reflexivity; lia. }
  pose proof (lookup_file_segment_at _ _ _ _ Hkeys Hlookup) as Hfile.
  unfold endpointInputMemory.
  apply lookup_union_Some_l.
  apply lookup_union_Some_l.
  exact Hfile.
Qed.
