Require Import ZesuSsz.Automation.All.
From Coq Require Import ZArith.ZArith.
From stdpp Require Import gmap list_numbers.
Require Import isla.opsem.
Require Import ZesuSsz.Contracts.ElfMemory.
Require Import ZesuMachineMap.Machine.
Require Import ZesuSsz.Generated.ElfImage.

Open Scope Z_scope.

Definition endpointDeviceAddresses : gset addr :=
  list_to_set (Z_to_bv 64 <$> seqZ (machineOutputAddress defaultMap) 24).

Lemma endpoint_device_address address :
  address ∈ endpointDeviceAddresses <->
  exists byteAddress,
    machineOutputAddress defaultMap <= byteAddress < machineExitAddress defaultMap + 8 /\
    address = Z_to_bv 64 byteAddress.
Proof.
  unfold endpointDeviceAddresses.
  rewrite elem_of_list_to_set elem_of_list_fmap.
  setoid_rewrite elem_of_seqZ. cbn. naive_solver.
Qed.

Definition endpointStackStart : Z := machineExitAddress defaultMap + 8.
Definition endpointStackEnd : Z := machineRamEnd defaultMap - 0x1000.
Definition endpointStackMemory : mem_map :=
  zeroSegment endpointStackStart (endpointStackEnd - endpointStackStart).

Lemma endpoint_stack_domain address :
  address ∈ dom endpointStackMemory <->
  exists byteAddress, endpointStackStart <= byteAddress < endpointStackEnd /\
    address = Z_to_bv 64 byteAddress.
Proof.
  unfold endpointStackMemory. rewrite dom_zero_segment.
  replace (endpointStackStart + (endpointStackEnd - endpointStackStart))
    with endpointStackEnd by lia. done.
Qed.

Lemma endpoint_stack_lookup address :
  endpointStackMemory !! address = Some (BV 8 0) <->
  exists byteAddress, endpointStackStart <= byteAddress < endpointStackEnd /\
    address = Z_to_bv 64 byteAddress.
Proof.
  unfold endpointStackMemory. rewrite lookup_zero_segment.
  replace (endpointStackStart + (endpointStackEnd - endpointStackStart))
    with endpointStackEnd by lia. done.
Qed.

Lemma endpoint_stack_outside address :
  0 <= address < bv_modulus 64 ->
  (address < endpointStackStart \/ endpointStackEnd <= address) ->
  endpointStackMemory !! Z_to_bv 64 address = None.
Proof.
  intros Haddress Houtside. unfold endpointStackMemory.
  apply lookup_zero_segment_outside.
  - unfold endpointStackStart. cbn. lia.
  - unfold endpointStackStart, endpointStackEnd.
    replace (bv_modulus 64) with 18446744073709551616 by reflexivity.
    cbn. lia.
  - exact Haddress.
  - replace (endpointStackStart + (endpointStackEnd - endpointStackStart))
      with endpointStackEnd by lia. exact Houtside.
Qed.

Local Opaque fileSegment elfRxBytes elfRwBytes.
Global Opaque endpointStackMemory.

Lemma endpoint_stack_elf_disjoint :
  dom endpointStackMemory ## dom (elfLoadMemoryExcept endpointDeviceAddresses).
Proof.
  apply elem_of_disjoint. intros address Hstack Helf.
  apply endpoint_stack_domain in Hstack.
  destruct Hstack as [stackAddress [Hstack ->]].
  apply elem_of_dom in Helf. destruct Helf as [value Helf].
  have Hnone : elfLoadMemoryExcept endpointDeviceAddresses !!
      Z_to_bv 64 stackAddress = None.
  { unfold elfLoadMemoryExcept. apply lookup_union_None. split.
    - apply lookup_union_None. split.
      + apply lookup_file_segment_outside. all: rewrite ?elf_rx_length.
        all: replace (Z.of_nat 0x8038) with 0x8038 by reflexivity.
        all: unfold endpointStackStart, endpointStackEnd in Hstack.
        all: cbn in *; replace (bv_modulus 64) with 18446744073709551616
          in * by reflexivity; lia.
      + apply lookup_file_segment_outside. all: rewrite ?elf_rw_length.
        all: unfold endpointStackStart, endpointStackEnd in Hstack.
        all: cbn in *; replace (bv_modulus 64) with 18446744073709551616
          in * by reflexivity; lia.
    - apply not_elem_of_dom. rewrite dom_zero_segment_except.
      intros [[source [Hrange Heq]] _].
      apply (f_equal bv_unsigned) in Heq.
      unfold endpointStackStart, endpointStackEnd in Hstack.
      rewrite !Z_to_bv_small in Heq; cbn in *;
        replace (bv_modulus 64) with 18446744073709551616 in * by reflexivity; lia. }
  rewrite Hnone in Helf. discriminate.
Qed.

Lemma endpoint_stack_input_disjoint input :
  (List.length input <= 64 * 1024 * 1024)%nat ->
  dom endpointStackMemory ## dom (fileSegment (mapInputBufferAddress defaultMap)
    (List.map (Z_to_bv 8) input)).
Proof.
  intros Hbound. apply elem_of_disjoint. intros address Hstack Hinput.
  apply endpoint_stack_domain in Hstack.
  destruct Hstack as [stackAddress [Hstack ->]].
  apply dom_file_segment_range in Hinput.
  destruct Hinput as [source [Hrange Heq]]. rewrite length_fmap in Hrange.
  apply (f_equal bv_unsigned) in Heq.
  unfold endpointStackStart, endpointStackEnd in Hstack.
  rewrite !Z_to_bv_small in Heq; cbn in *;
    replace (bv_modulus 64) with 18446744073709551616 in * by reflexivity; lia.
Qed.

Lemma endpoint_stack_context_disjoint (input : list Z) :
  dom endpointStackMemory ## dom (fileSegment (mapIoContextAddress defaultMap)
    (bv_to_little_endian 8 8 (Z.of_nat (List.length input)))).
Proof.
  apply elem_of_disjoint. intros address Hstack Hcontext.
  apply endpoint_stack_domain in Hstack.
  destruct Hstack as [stackAddress [Hstack ->]].
  apply dom_file_segment_range in Hcontext.
  destruct Hcontext as [source [Hrange Heq]].
  rewrite length_bv_to_little_endian in Hrange; last lia.
  apply (f_equal bv_unsigned) in Heq.
  unfold endpointStackStart, endpointStackEnd in Hstack.
  rewrite !Z_to_bv_small in Heq; cbn in *;
    replace (bv_modulus 64) with 18446744073709551616 in * by reflexivity; lia.
Qed.

Lemma endpoint_stack_device_disjoint :
  dom endpointStackMemory ## endpointDeviceAddresses.
Proof.
  apply elem_of_disjoint. intros address Hstack Hdevice.
  apply endpoint_stack_domain in Hstack. apply endpoint_device_address in Hdevice.
  destruct Hstack as [stackAddress [Hstack ->]].
  destruct Hdevice as [source [Hrange Heq]].
  apply (f_equal bv_unsigned) in Heq.
  unfold endpointStackStart, endpointStackEnd in Hstack.
  rewrite !Z_to_bv_small in Heq; cbn in *;
    replace (bv_modulus 64) with 18446744073709551616 in * by reflexivity; lia.
Qed.

Definition endpointInputMemory (input : list Z) : mem_map :=
  fileSegment (mapInputBufferAddress defaultMap)
    (List.map (Z_to_bv 8) input) ∪
  fileSegment (mapIoContextAddress defaultMap)
    (bv_to_little_endian 8 8 (Z.of_nat (List.length input))) ∪
  elfLoadMemoryExcept endpointDeviceAddresses ∪ endpointStackMemory.

Lemma endpoint_stack_initial_disjoint input :
  (List.length input <= 64 * 1024 * 1024)%nat ->
  dom endpointStackMemory ##
    dom (fileSegment (mapInputBufferAddress defaultMap)
      (List.map (Z_to_bv 8) input) ∪
      fileSegment (mapIoContextAddress defaultMap)
        (bv_to_little_endian 8 8 (Z.of_nat (List.length input))) ∪
      elfLoadMemoryExcept endpointDeviceAddresses).
Proof.
  intros Hbound. apply elem_of_disjoint. intros address Hstack Hinitial.
  apply elem_of_dom in Hinitial. destruct Hinitial as [value Hinitial].
  have Hnone : (fileSegment (mapInputBufferAddress defaultMap)
      (List.map (Z_to_bv 8) input) ∪
      fileSegment (mapIoContextAddress defaultMap)
        (bv_to_little_endian 8 8 (Z.of_nat (List.length input))) ∪
      elfLoadMemoryExcept endpointDeviceAddresses) !! address = None.
  { apply lookup_union_None. split.
    - apply lookup_union_None. split.
      + apply not_elem_of_dom. intros Hinput.
        exact ((proj1 (elem_of_disjoint _ _)) (endpoint_stack_input_disjoint input Hbound)
          address Hstack Hinput).
      + apply not_elem_of_dom. intros Hcontext.
        exact ((proj1 (elem_of_disjoint _ _)) (endpoint_stack_context_disjoint input)
          address Hstack Hcontext).
    - apply not_elem_of_dom. intros Helf.
      exact ((proj1 (elem_of_disjoint _ _)) endpoint_stack_elf_disjoint address Hstack Helf). }
  rewrite Hnone in Hinitial. discriminate.
Qed.

Lemma endpoint_stack_byte input address :
  (List.length input <= 64 * 1024 * 1024)%nat ->
  endpointStackStart <= address < endpointStackEnd ->
  endpointInputMemory input !! Z_to_bv 64 address = Some (BV 8 0).
Proof.
  intros Hbound Hrange.
  have Hstack : Z_to_bv 64 address ∈ dom endpointStackMemory.
  { apply endpoint_stack_domain. exists address. auto. }
  unfold endpointInputMemory. rewrite lookup_union_r.
  - apply endpoint_stack_lookup. exists address. auto.
  - apply not_elem_of_dom. intros Hinitial.
    exact ((proj1 (elem_of_disjoint _ _)) (endpoint_stack_initial_disjoint input Hbound)
      (Z_to_bv 64 address) Hstack Hinitial).
Qed.

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
  apply lookup_union_Some_l.
  exact Hfile.
Qed.

Lemma endpoint_device_unbacked input address :
  (List.length input <= 64 * 1024 * 1024)%nat ->
  address ∈ endpointDeviceAddresses ->
  endpointInputMemory input !! address = None.
Proof.
  intros Hbound Hdevice. pose proof Hdevice as HdeviceOriginal.
  apply endpoint_device_address in Hdevice.
  destruct Hdevice as [byteAddress [Hrange ->]].
  unfold endpointInputMemory. apply lookup_union_None. split.
  - {
    apply lookup_union_None. split.
  - apply lookup_union_None. split.
    + apply lookup_file_segment_outside; rewrite ?length_fmap; cbn;
        replace (bv_modulus 64) with 18446744073709551616 by reflexivity; lia.
    + apply lookup_file_segment_outside; rewrite ?length_bv_to_little_endian; cbn;
        replace (bv_modulus 64) with 18446744073709551616 by reflexivity; lia.
  - unfold elfLoadMemoryExcept. apply lookup_union_None. split.
    + apply lookup_union_None. split.
      * apply (lookup_file_segment_outside 0x10000 elfRxBytes byteAddress).
        all: rewrite ?elf_rx_length.
        all: replace (Z.of_nat 0x8038) with 0x8038 by reflexivity.
        all: replace (bv_modulus 64) with 18446744073709551616 by reflexivity.
        all: cbn in Hrange; lia.
      * apply (lookup_file_segment_outside 0x19000 elfRwBytes byteAddress);
          rewrite ?elf_rw_length; cbn;
          replace (bv_modulus 64) with 18446744073709551616 by reflexivity; lia.
    + apply lookup_zero_segment_except_none. exact HdeviceOriginal.
    }
  - apply endpoint_stack_outside.
    + cbn in Hrange; replace (bv_modulus 64) with 18446744073709551616
        by reflexivity; lia.
    + unfold endpointStackStart. lia.
Qed.

Lemma endpoint_device_range_unbacked input :
  (List.length input <= 64 * 1024 * 1024)%nat ->
  set_Forall (fun address =>
    ~ (machineOutputAddress defaultMap <= bv_unsigned address <
       machineExitAddress defaultMap + 8)) (dom (endpointInputMemory input)).
Proof.
  intros Hbound address Hdom Hrange.
  have Hdevice : address ∈ endpointDeviceAddresses.
  { apply endpoint_device_address. exists (bv_unsigned address).
    split; first exact Hrange. symmetry. apply Z_to_bv_bv_unsigned. }
  apply elem_of_dom in Hdom. destruct Hdom as [byte Hlookup].
  rewrite (endpoint_device_unbacked input address Hbound Hdevice) in Hlookup.
  discriminate.
Qed.

Print Assumptions endpoint_input_byte.
Print Assumptions endpoint_device_address.
Print Assumptions endpoint_device_unbacked.
Print Assumptions endpoint_device_range_unbacked.

Print Assumptions endpoint_stack_domain.
Print Assumptions endpoint_stack_lookup.
Print Assumptions endpoint_stack_outside.
Print Assumptions endpoint_stack_elf_disjoint.
Print Assumptions endpoint_stack_input_disjoint.
Print Assumptions endpoint_stack_context_disjoint.
Print Assumptions endpoint_stack_device_disjoint.
Print Assumptions endpoint_stack_initial_disjoint.
Print Assumptions endpoint_stack_byte.
