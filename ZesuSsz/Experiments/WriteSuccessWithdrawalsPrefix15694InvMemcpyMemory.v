From Coq Require Import Lia Lists.List ZArith.ZArith.
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Contracts.IslaMemoryOperational.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsOperational.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsPrefix15694InvMemcpyState.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsPrefix15694InvMemcpySupport.

Open Scope Z_scope.

Lemma writeSuccessWithdrawalsPrefix15694MemcpyMemory args sp pointer base total
    processed remaining withdrawal allBytes prefix current suffix scratch
    encoderScratch registerFrame memoryFrame priorLog state :
  Inv_15694 args sp pointer base total processed remaining withdrawal allBytes
    prefix current suffix scratch encoderScratch registerFrame memoryFrame
    priorLog state ->
  read_mem_list state.1.2.(seq_mem) (bv_unsigned pointer)
      (N.of_nat (length current)) = Some current /\
  read_mem_list state.1.2.(seq_mem) (bv_unsigned (sp + BV 64 1744)%bv)
      (N.of_nat (length current)) = Some scratch /\
  islaMemoryRange (bv_unsigned (sp + BV 64 1744)%bv) (length current) /\
  0x20000000 <= bv_unsigned pointer /\
  bv_unsigned pointer + Z.of_nat (length current) <= 0x40000000 /\
  0x20000000 <= bv_unsigned (sp + BV 64 1744)%bv /\
  bv_unsigned (sp + BV 64 1744)%bv + Z.of_nat (length current) <= 0x40000000 /\
  islaMemoryRangesDisjoint (bv_unsigned (sp + BV 64 1744)%bv) (length current)
    (bv_unsigned pointer) (length current) /\
  (forall location,
    bv_unsigned (sp + BV 64 1744)%bv <= location <
      bv_unsigned (sp + BV 64 1744)%bv + Z.of_nat (length current) ->
    is_Some (state.1.2.(seq_mem) !! Z_to_bv 64 location)) /\
  writeSuccessMemoryRangeFrame (bv_unsigned (sp + BV 64 1744)%bv)
    (length current) state.1.2.(seq_mem) state.1.2.(seq_mem).
Proof.
  intros Hinv.
  have Hsource : read_mem_list state.1.2.(seq_mem) (bv_unsigned pointer) 48%N =
      Some current by (unfold Inv_15694 in Hinv; tauto).
  have Hdestination : read_mem_list state.1.2.(seq_mem)
      (bv_unsigned sp + 1744) 48%N = Some scratch by
    (unfold Inv_15694 in Hinv; tauto).
  have Hdisjoint : islaMemoryRangesDisjoint (bv_unsigned pointer) 48
      (bv_unsigned sp + 1744) 48 by (unfold Inv_15694 in Hinv; tauto).
  have HspLower : 0x20000000 <= bv_unsigned sp - 16 by
    (unfold Inv_15694 in Hinv; tauto).
  have HspUpper : bv_unsigned sp + 1792 < 0x40000000 by
    (unfold Inv_15694 in Hinv; tauto).
  have HbaseLower : 0x20000000 <= base by
    (unfold Inv_15694 in Hinv; tauto).
  have HbaseUpper : base + Z.of_nat (length allBytes) < 0x40000000 by
    (unfold Inv_15694 in Hinv; tauto).
  have Hpointer : bv_unsigned pointer = base + 48 * Z.of_nat processed by
    (unfold Inv_15694 in Hinv; tauto).
  have HallBytes : allBytes = prefix ++ current ++ suffix by
    (unfold Inv_15694 in Hinv; tauto).
  have Hprefix : length prefix = (48 * processed)%nat by
    (unfold Inv_15694 in Hinv; tauto).
  have Hcurrent : length current = 48%nat by
    (unfold Inv_15694 in Hinv; tauto).
  have HdestinationUnsigned :=
    writeSuccessWithdrawalsPrefixDestinationUnsigned sp HspUpper.
  have HsourceLower : 0x20000000 <= bv_unsigned pointer by lia.
  have HsourceUpper : bv_unsigned pointer + Z.of_nat (length current) <=
      0x40000000.
  { rewrite Hcurrent. rewrite HallBytes !app_length in HbaseUpper.
    rewrite Hprefix in HbaseUpper. lia. }
  have HdestinationLower : 0x20000000 <=
      bv_unsigned (sp + BV 64 1744)%bv by (rewrite HdestinationUnsigned; lia).
  have HdestinationUpper : bv_unsigned (sp + BV 64 1744)%bv +
      Z.of_nat (length current) <= 0x40000000 by
    (rewrite HdestinationUnsigned Hcurrent; lia).
  have Hrange : islaMemoryRange (bv_unsigned (sp + BV 64 1744)%bv)
      (length current).
  { unfold islaMemoryRange. rewrite HdestinationUnsigned Hcurrent.
    split; lia. }
  have Hdisjoint' : islaMemoryRangesDisjoint
      (bv_unsigned (sp + BV 64 1744)%bv) (length current)
      (bv_unsigned pointer) (length current).
  { rewrite HdestinationUnsigned Hcurrent. unfold islaMemoryRangesDisjoint in *.
    destruct Hdisjoint; [right|left]; lia. }
  have Hbacked : forall location,
      bv_unsigned (sp + BV 64 1744)%bv <= location <
        bv_unsigned (sp + BV 64 1744)%bv + Z.of_nat (length current) ->
      is_Some (state.1.2.(seq_mem) !! Z_to_bv 64 location).
  { intros location Hlocation. rewrite HdestinationUnsigned Hcurrent in Hlocation.
    apply (writeSuccessReadMemListBacked state.1.2.(seq_mem)
      (bv_unsigned sp + 1744) 48 scratch Hdestination location).
    exact Hlocation. }
  split; first (rewrite Hcurrent; exact Hsource).
  split; first (rewrite HdestinationUnsigned Hcurrent; exact Hdestination).
  split; first exact Hrange.
  split; first exact HsourceLower.
  split; first exact HsourceUpper.
  split; first exact HdestinationLower.
  split; first exact HdestinationUpper.
  split; first exact Hdisjoint'.
  split; first exact Hbacked.
  split; first reflexivity. intros address _. reflexivity.
Qed.

Print Assumptions writeSuccessWithdrawalsPrefix15694MemcpyMemory.
