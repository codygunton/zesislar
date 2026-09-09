From Coq Require Import Lia Lists.List ZArith.ZArith.
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Contracts.IslaMemoryOperational.
Require Import ZesuSsz.Experiments.WriteSuccessSegment101d8.
Require Import ZesuSsz.Experiments.WriteSuccessSegment101e4.
Require Import ZesuSsz.Experiments.WriteSuccessSegment101f0.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsOperational.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsOperationalData.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsMemcpyByteRun.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsMemcpyInduction.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsMemcpyMemory.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsMemcpyIterationMemory.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsMemcpyReadinessFacts.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsMemcpyState.

Import ListNotations.
Open Scope Z_scope.

Local Opaque writeSuccessWithdrawalsOperationalRegisterFacts.

Theorem writeSuccessMemcpyBytesReadyFromMemory
    (regs : reg_map) (global : seq_global_state)
    (source destination totalLength : bv 64)
    (allBytes prefix remaining : list (bv 8)) :
  allBytes = prefix ++ remaining ->
  regs !! "PC" = Some (RVal_Bits (Z_to_bv 64 0x101d8)) ->
  regs !! "x10" = Some (RVal_Bits destination) ->
  regs !! "x11" = Some (RVal_Bits source) ->
  regs !! "x12" = Some (RVal_Bits totalLength) ->
  regs !! "x15" = Some (RVal_Bits (Z_to_bv 64 (Z.of_nat (length prefix)))) ->
  totalLength = Z_to_bv 64 (Z.of_nat (length allBytes)) ->
  writeSuccessWithdrawalsInstructionTable global ->
  writeSuccessWithdrawalsOperationalRegisterFacts regs ->
  read_mem_list global.(seq_mem) (bv_unsigned source)
    (N.of_nat (length allBytes)) = Some allBytes ->
  islaMemoryRange (bv_unsigned destination) (length allBytes) ->
  0x20000000 <= bv_unsigned source ->
  bv_unsigned source + Z.of_nat (length allBytes) <= 0x40000000 ->
  0x20000000 <= bv_unsigned destination ->
  bv_unsigned destination + Z.of_nat (length allBytes) <= 0x40000000 ->
  islaMemoryRangesDisjoint (bv_unsigned destination) (length allBytes)
    (bv_unsigned source) (length allBytes) ->
  (forall location,
    bv_unsigned destination <= location <
      bv_unsigned destination + Z.of_nat (length allBytes) ->
    is_Some (global.(seq_mem) !! Z_to_bv 64 location)) ->
  writeSuccessMemcpyBytesReady regs global source destination
    (Z_to_bv 64 (Z.of_nat (length prefix))) totalLength remaining.
Proof.
  revert regs global prefix.
  induction remaining as [|byte tail IH]; intros regs global prefix
    Hall Hpc Hx10 Hx11 Hx12 Hx15 Hlength Htable Hfacts Hsource Hrange
    HsourceLower HsourceUpper HdestinationLower HdestinationUpper Hdisjoint
    Hbacked.
  - cbn. exact I.
  - cbn.
    have HprefixLt : (length prefix < length allBytes)%nat by
      (rewrite Hall; rewrite app_length; cbn; lia).
    have HprefixLtZ : Z.of_nat (length prefix) <
        Z.of_nat (length allBytes) by lia.
    have HindexBounds : 0 <= Z.of_nat (length prefix) <=
        Z.of_nat (length allBytes) by lia.
    have HsourceNonnegative := bv_unsigned_in_range 64 source.
    have HtotalBound : Z.of_nat (length allBytes) < 2 ^ 64 by
      (unfold bv_modulus in HsourceNonnegative; cbn in *; lia).
    have Hneq : Z_to_bv 64 (Z.of_nat (length prefix)) <> totalLength by
      (rewrite Hlength; apply writeSuccessMemcpyIndexDifferent; lia).
    split.
    + unfold writeSuccessMemcpyByteReady. repeat split.
      * exact Hpc.
      * exact Hx10.
      * exact Hx11.
      * exact Hx12.
      * exact Hx15.
      * exact Hneq.
      * exact Htable.
      * exact (proj1 Hfacts).
      * exact (proj1 (proj2 Hfacts)).
      * exact (proj2 (proj2 Hfacts)).
      * have Hnth : nth_error allBytes (length prefix) = Some byte by
          (rewrite Hall; rewrite nth_error_app2; last lia;
           replace (length prefix - length prefix)%nat with 0%nat by lia;
           reflexivity).
        have Hread := writeSuccessMemcpyReadByte global.(seq_mem)
          (bv_unsigned source) allBytes (length prefix) byte Hsource Hnth.
        unfold writeSuccessMemcpySourceAddress.
        rewrite (writeSuccessMemcpyAddressAt source
          (Z.of_nat (length prefix)) (Z.of_nat (length allBytes)));
          try lia; exact Hread.
      * unfold writeSuccessMemcpySourceAddress.
        rewrite (writeSuccessMemcpyAddressAt source (Z.of_nat (length prefix))
          (Z.of_nat (length allBytes))); try lia.
      * unfold writeSuccessMemcpySourceAddress.
        rewrite (writeSuccessMemcpyAddressAt source (Z.of_nat (length prefix))
          (Z.of_nat (length allBytes))); try lia.
      * unfold writeSuccessMemcpyDestinationAddress.
        rewrite (writeSuccessMemcpyAddressAt destination (Z.of_nat (length prefix))
          (Z.of_nat (length allBytes))); try lia.
      * unfold writeSuccessMemcpyDestinationAddress.
        rewrite (writeSuccessMemcpyAddressAt destination (Z.of_nat (length prefix))
          (Z.of_nat (length allBytes))); try lia.
      * unfold writeSuccessMemcpyDestinationAddress.
        rewrite (writeSuccessMemcpyAddressAtBv destination
          (Z.of_nat (length prefix)) (Z.of_nat (length allBytes)));
          try lia. apply Hbacked.
        rewrite Hall. rewrite app_length. cbn. lia.
    + replace (Z_to_bv 64 (Z.of_nat (length prefix)) + BV 64 1)%bv with
        (Z_to_bv 64 (Z.of_nat (length (prefix ++ [byte])))) by
        (rewrite app_length; cbn; apply bv_eq; bv_solve).
      apply (IH
        (writeSuccessMemcpyByteRegs regs source destination
          (Z_to_bv 64 (Z.of_nat (length prefix))) byte)
        (writeSuccess101f0Global global
          (writeSuccessMemcpyDestinationAddress destination
            (Z_to_bv 64 (Z.of_nat (length prefix))))
          (writeSuccess101e4Loaded byte))
        (prefix ++ [byte])).
      * rewrite Hall. rewrite <- app_assoc. reflexivity.
      * apply writeSuccessMemcpyByteRegsPc.
      * rewrite writeSuccessMemcpyByteRegsLookupOther; try discriminate.
        exact Hx10.
      * rewrite writeSuccessMemcpyByteRegsLookupOther; try discriminate.
        exact Hx11.
      * rewrite writeSuccessMemcpyByteRegsLookupOther; try discriminate.
        exact Hx12.
      * rewrite writeSuccessMemcpyByteRegsX15. repeat f_equal.
        rewrite app_length. cbn. apply bv_eq. bv_solve.
      * exact Hlength.
      * unfold writeSuccess101f0Global. cbn. exact Htable.
      * apply writeSuccessMemcpyByteOperationalFacts. exact Hfacts.
      * unfold writeSuccess101f0Global, writeSuccess101f0Memory. cbn.
        rewrite writeSuccessMemcpyStoredByte.
        unfold writeSuccessMemcpyDestinationAddress.
        rewrite (writeSuccessMemcpyAddressAtBv destination
          (Z.of_nat (length prefix)) (Z.of_nat (length allBytes))
          HindexBounds HdestinationUpper).
        eapply read_mem_list_write_mem_list_disjoint.
        { unfold islaMemoryRange. cbn. split; first lia.
          have HdestinationRange := bv_unsigned_in_range 64 destination.
          unfold bv_modulus in HdestinationRange. cbn in *. lia. }
        { apply writeSuccessMemcpyOneByteDisjoint with
            (index := length prefix) (total := length allBytes).
          { rewrite Hall. rewrite app_length. cbn. lia. }
          { exact Hdisjoint. } }
        { exact Hsource. }
      * exact Hrange.
      * exact HsourceLower.
      * exact HsourceUpper.
      * exact HdestinationLower.
      * exact HdestinationUpper.
      * exact Hdisjoint.
      * intros location Hlocation. unfold writeSuccess101f0Global,
          writeSuccess101f0Memory. cbn. rewrite writeSuccessMemcpyStoredByte.
        unfold writeSuccessMemcpyDestinationAddress.
        rewrite (writeSuccessMemcpyAddressAtBv destination
          (Z.of_nat (length prefix)) (Z.of_nat (length allBytes))
          HindexBounds HdestinationUpper).
        apply elem_of_dom.
        rewrite write_mem_list_dom.
        { apply elem_of_dom. apply Hbacked. exact Hlocation. }
        { unfold islaMemoryRange. cbn. split; first lia.
          have HdestinationRange := bv_unsigned_in_range 64 destination.
          unfold bv_modulus in HdestinationRange. cbn in *. lia. }
        { intros written Hwritten. apply Hbacked.
          rewrite Hall. rewrite app_length. cbn. split; first lia.
          cbn in Hwritten.
          have HtailNonnegative := Nat2Z.is_nonneg (length tail). lia. }
Qed.

Print Assumptions writeSuccessMemcpyBytesReadyFromMemory.
