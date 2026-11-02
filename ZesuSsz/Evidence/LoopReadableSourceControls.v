Require Import ZesuSsz.Automation.All.
Require Import ZesuSsz.Automation.LoopReadableRegions.
Require Import ZesuSsz.Automation.BitvectorFacts.
Require Import ZesuSsz.Evidence.LoopSourceReadControls.
Require Import ZesuSsz.Contracts.RlpDecodeItemContract.
Require Import ZesuSsz.Contracts.RlpDecodeItem.
Require Import ZesuMachineMap.Machine.
From Coq Require Import Lists.List ZArith.ZArith Lia Bool.Bool.
From stdpp Require Import bitvector.definitions decidable.
Open Scope Z_scope.

Lemma loop_readable_from_complete_source_domain (args : DecodeItemArgs) (returnAddress index : Z)
    (cursor endpoint length_word count : bv 64) :
  decodeItemDomainAt returnAddress decodeItemC1BDomain args ->
  length_word = Z_to_bv 64 (decodeItemInputLength args) ->
  endpoint = bv_add (Z_to_bv 64 (decodeItemInputPointer args)) (bv_add count (BV 64 1)) ->
  0 <= index -> bv_unsigned cursor = decodeItemInputPointer args + 1 + index ->
  bv_unsigned cursor < bv_unsigned endpoint ->
  negb (bool_decide (bv_signed (bv_zero_extend 128 count) >=
                    bv_signed (bv_zero_extend 128 length_word))) = true ->
  ((mapInputBufferAddress defaultMap <= bv_unsigned cursor /\
    bv_unsigned cursor + 1 <= mapInputBufferAddress defaultMap + mapInputCapacity defaultMap) \/
   (mapRamBase defaultMap <= bv_unsigned cursor /\
    bv_unsigned cursor + 1 <= machineRamEnd defaultMap)).
Proof.
  intros Hdomain HlengthWord Hendpoint Hindex Horigin Hhead HcountGuard.
  pose proof (loop_read_from_complete_source_domain args returnAddress index cursor endpoint
    length_word count Hdomain HlengthWord Hendpoint Hindex Horigin Hhead HcountGuard)
    as [Hread Hlookup].
  unfold decodeItemDomainAt, decodeItemC1BDomain, decodeItemArgsWellFormed,
    decodeItemEntryLayout in Hdomain.
  repeat match goal with Hpart : _ /\ _ |- _ => destruct Hpart end.
  eapply (zesu_loop_readable_window (decodeItemInputPointer args) (decodeItemInputLength args)
    (bv_unsigned cursor) 1 (mapInputBufferAddress defaultMap)
    (mapInputBufferAddress defaultMap + mapInputCapacity defaultMap)
    (mapRamBase defaultMap) (machineRamEnd defaultMap)); [eassumption | lia | lia].
Qed.

Lemma loop_ram_upper_fault_from_complete_source_domain (args : DecodeItemArgs) (returnAddress index : Z)
    (cursor endpoint length_word count : bv 64) :
  decodeItemDomainAt returnAddress decodeItemC1BDomain args ->
  length_word = Z_to_bv 64 (decodeItemInputLength args) ->
  endpoint = bv_add (Z_to_bv 64 (decodeItemInputPointer args)) (bv_add count (BV 64 1)) ->
  0 <= index -> bv_unsigned cursor = decodeItemInputPointer args + 1 + index ->
  bv_unsigned cursor < bv_unsigned endpoint ->
  negb (bool_decide (bv_signed (bv_zero_extend 128 count) >=
                    bv_signed (bv_zero_extend 128 length_word))) = true ->
  bool_decide (bv_signed (bv_zero_extend 128 cursor) >= bv_signed (BV 128 2684354560)) = true ->
  negb (bool_decide (bv_signed (bv_add (bv_zero_extend 128 cursor) (BV 128 1)) <=
                    bv_signed (BV 128 3221225472))) = true -> False.
Proof.
  intros Hdomain HlengthWord Hendpoint Hindex Horigin Hhead HcountGuard Hlower Houtside.
  pose proof (loop_readable_from_complete_source_domain args returnAddress index cursor endpoint
    length_word count Hdomain HlengthWord Hendpoint Hindex Horigin Hhead HcountGuard) as Hreadable.
  apply bool_decide_eq_true_1 in Hlower.
  rewrite zesu_signed_zero_extend_64_128 in Hlower.
  change (bv_unsigned cursor >= 2684354560) in Hlower.
  apply Bool.negb_true_iff in Houtside. apply bool_decide_eq_false_1 in Houtside.
  rewrite (zesu_signed_zero_extend_add_64_128 cursor (BV 128 1)
    ltac:(change (1 < 18446744073709551616); lia)) in Houtside.
  change (~ (bv_unsigned cursor + 1 <= 3221225472)) in Houtside.
  change ((1073741824 <= bv_unsigned cursor /\ bv_unsigned cursor + 1 <= 2147483648) \/
    (2684354560 <= bv_unsigned cursor /\ bv_unsigned cursor + 1 <= 3221225472)) in Hreadable.
  eapply (zesu_loop_readable_upper_refutation (bv_unsigned cursor) 1
    1073741824 2147483648 2684354560 3221225472); [exact Hreadable | lia | lia | lia | exact Houtside].
Qed.
