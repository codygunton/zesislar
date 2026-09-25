Require Import ZesuSsz.Automation.All.
From Coq Require Import ZArith.ZArith.
From stdpp Require Import gmap list_numbers.
Require Import isla.opsem.
Require Import ZesuSsz.Generated.ElfImage.
Require Import ZesuMachineMap.Machine.

Definition zeroSegment (start length : Z) : mem_map :=
  gset_to_gmap (BV 8 0)
    (list_to_set (List.map (Z_to_bv 64) (seqZ start length)) : gset addr).

Definition fileSegment (start : Z) (bytes : list (bv 8)) : mem_map :=
  list_to_map (zip
    (List.map (Z_to_bv 64) (seqZ start (Z.of_nat (List.length bytes))))
    bytes).

Lemma lookup_file_segment start bytes address value :
  fileSegment start bytes !! address = Some value ->
  (address, value) ∈ zip
    (List.map (Z_to_bv 64) (seqZ start (Z.of_nat (List.length bytes))))
    bytes.
Proof. exact (elem_of_list_to_map_2 _ _ _). Qed.

Lemma file_segment_keys_nodup start (bytes : list (bv 8)) :
  NoDup (List.map (Z_to_bv 64)
    (seqZ start (Z.of_nat (List.length bytes)))) ->
  NoDup ((zip
    (List.map (Z_to_bv 64) (seqZ start (Z.of_nat (List.length bytes))))
    bytes).*1).
Proof.
  rewrite fst_zip; [done|].
  rewrite length_fmap length_seqZ Nat2Z.id. lia.
Qed.

Lemma bounded_segment_keys_nodup start length :
  0 <= start -> start + length <= bv_modulus 64 ->
  NoDup (List.map (Z_to_bv 64) (seqZ start length)).
Proof.
  intros Hstart Hend.
  apply NoDup_fmap_2_strong; last apply NoDup_seqZ.
  intros x y Hx Hy Heq.
  apply elem_of_seqZ in Hx.
  apply elem_of_seqZ in Hy.
  apply (f_equal bv_unsigned) in Heq.
  rewrite !Z_to_bv_small in Heq; [exact Heq | lia | lia].
Qed.

Lemma lookup_file_segment_at start bytes offset value :
  NoDup (List.map (Z_to_bv 64)
    (seqZ start (Z.of_nat (List.length bytes)))) ->
  bytes !! offset = Some value ->
  fileSegment start bytes !! (Z_to_bv 64 (start + Z.of_nat offset)) =
    Some value.
Proof.
  intros Hkeys Hbyte.
  apply elem_of_list_to_map_1.
  - apply file_segment_keys_nodup. exact Hkeys.
  - apply elem_of_list_lookup. exists offset.
    rewrite lookup_zip_with list_lookup_fmap.
    rewrite lookup_seqZ_lt; [rewrite Hbyte; reflexivity|].
    apply lookup_lt_Some in Hbyte. lia.
Qed.

Lemma lookup_file_segment_outside start bytes address :
  0 <= start ->
  start + Z.of_nat (List.length bytes) <= bv_modulus 64 ->
  0 <= address < bv_modulus 64 ->
  (address < start \/ start + Z.of_nat (List.length bytes) <= address) ->
  fileSegment start bytes !! Z_to_bv 64 address = None.
Proof.
  intros Hstart Hend Haddress Houtside.
  apply not_elem_of_list_to_map_1.
  rewrite fst_zip.
  2: { rewrite length_fmap length_seqZ Nat2Z.id. lia. }
  intros Hin.
  apply elem_of_list_fmap in Hin.
  destruct Hin as [source [Heq Hsource]].
  apply elem_of_seqZ in Hsource.
  apply (f_equal bv_unsigned) in Heq.
  rewrite !Z_to_bv_small in Heq; [|lia|lia].
  lia.
Qed.

Lemma dom_file_segment start bytes address :
  address ∈ dom (fileSegment start bytes) <->
  address ∈ (zip
    (List.map (Z_to_bv 64) (seqZ start (Z.of_nat (List.length bytes))))
    bytes).*1.
Proof.
  rewrite elem_of_dom.
  split.
  - intros [value Hlookup].
    apply lookup_file_segment in Hlookup.
    apply elem_of_list_fmap. exists (address, value). simpl.
    split; [reflexivity | exact Hlookup].
  - intros Haddress.
    apply elem_of_list_fmap in Haddress.
    destruct Haddress as [[key value] [Heq Hin]]. simpl in Heq.
    subst key.
    destruct (fileSegment start bytes !! address) as [actual|] eqn:Hlookup.
    + eauto.
    + exfalso. apply (not_elem_of_list_to_map_2 _ _ Hlookup).
      apply elem_of_list_fmap. exists (address, value). simpl.
      split; [reflexivity | exact Hin].
Qed.

Lemma lookup_zero_segment start length address :
  zeroSegment start length !! address = Some (BV 8 0) <->
  exists byteAddress, start <= byteAddress < start + length /\
    address = Z_to_bv 64 byteAddress.
Proof.
  rewrite /zeroSegment lookup_gset_to_gmap_Some.
  rewrite elem_of_list_to_set elem_of_list_fmap.
  setoid_rewrite elem_of_seqZ.
  naive_solver.
Qed.

Lemma dom_zero_segment start length address :
  address ∈ dom (zeroSegment start length) <->
  exists byteAddress, start <= byteAddress < start + length /\
    address = Z_to_bv 64 byteAddress.
Proof.
  rewrite elem_of_dom. split.
  - intros [value Hlookup].
    rewrite lookup_gset_to_gmap_Some in Hlookup.
    destruct Hlookup as [Hin _].
    rewrite elem_of_list_to_set elem_of_list_fmap in Hin.
    setoid_rewrite elem_of_seqZ in Hin. naive_solver.
  - intros (byteAddress & Hrange & ->).
    eexists. apply lookup_zero_segment. naive_solver.
Qed.

Global Opaque zeroSegment.

Definition elfLoadMemory : mem_map :=
  fileSegment 0x10000 elfRxBytes ∪
  fileSegment 0x19000 elfRwBytes ∪
  zeroSegment 0x19010 0x240010c8.

Print Assumptions lookup_zero_segment.
Print Assumptions dom_zero_segment.
