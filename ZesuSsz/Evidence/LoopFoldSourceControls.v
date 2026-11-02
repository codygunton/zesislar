Require Import ZesuSsz.Automation.All.
Require Import ZesuSsz.Automation.ByteWindowFold.
Require Import ZesuSsz.Automation.ByteWindowFoldCursor.
Require Import ZesuSsz.Contracts.RlpDecodeItemContract.
Require Import ZesuSsz.Contracts.RlpDecodeItem.
Require Import ZesuSsz.Evidence.LoopSourceReadControls.
Require Import ZesuSsz.Evidence.LoopSourceIndexControls.
Require Import ZesuSsz.Evidence.LoopFoldCountControls.
From Coq Require Import Lists.List ZArith.ZArith Lia Bool.Bool.
From stdpp Require Import bitvector.definitions decidable.
Open Scope Z_scope.

Lemma loop_fold_step_from_complete_source_domain (args : DecodeItemArgs) (returnAddress index : Z)
    (cursor endpoint length_word count acc : bv 64) :
  decodeItemDomainAt returnAddress decodeItemC1BDomain args ->
  length_word = Z_to_bv 64 (decodeItemInputLength args) ->
  endpoint = bv_add (Z_to_bv 64 (decodeItemInputPointer args)) (bv_add count (BV 64 1)) ->
  0 <= index -> bv_unsigned cursor = decodeItemInputPointer args + 1 + index ->
  bv_unsigned cursor < bv_unsigned endpoint ->
  negb (bool_decide (bv_signed (bv_zero_extend 128 count) >=
                    bv_signed (bv_zero_extend 128 length_word))) = true ->
  bv_unsigned count <= 8 ->
  bv_unsigned acc = zesu_byte_window_fold (decodeItemInputBytes args) 1 (Z.to_nat index) ->
  bv_unsigned (bv_or (bv_shiftl acc (BV 64 8))
    (bv_zero_extend 64 (List.nth
      (Z.to_nat (bv_unsigned cursor - bv_unsigned (Z_to_bv 64 (decodeItemInputPointer args))))
      (decodeItemInputBytes args) (BV 8 0)))) =
    zesu_byte_window_fold (decodeItemInputBytes args) 1 (Z.to_nat (index + 1)).
Proof.
  intros Hdomain HlengthWord Hendpoint Hindex HcursorOrigin Hcursor HcountGuard Hwidth Hacc.
  pose proof (loop_owned_read_from_complete_source_domain args returnAddress index cursor endpoint
    length_word count Hdomain HlengthWord Hendpoint Hindex HcursorOrigin Hcursor HcountGuard)
    as [Hrange Hlookup].
  pose proof (loop_index_from_complete_source_domain args returnAddress index cursor endpoint
    length_word count Hdomain HlengthWord Hendpoint Hindex HcursorOrigin Hcursor HcountGuard)
    as HindexCount.
  assert (HbaseView : bv_unsigned (Z_to_bv 64 (decodeItemInputPointer args)) = decodeItemInputPointer args).
  { pose proof Hdomain as Hsource.
    unfold decodeItemDomainAt, decodeItemC1BDomain, decodeItemArgsWellFormed,
      decodeItemEntryLayout in Hsource.
    repeat match goal with Hpart : _ /\ _ |- _ => destruct Hpart end.
    apply Z_to_bv_small. unfold bv_modulus, word64Modulus in *. lia. }
  eapply (zesu_byte_window_cursor_step (decodeItemInputBytes args)
    (Z_to_bv 64 (decodeItemInputPointer args)) cursor 1 index (bv_unsigned count) acc);
    [exact Hindex | exact HindexCount | exact Hwidth | | exact Hacc | exact Hlookup].
  rewrite HbaseView. simpl. exact HcursorOrigin.
Qed.

Lemma loop_fold_source_6a24 (args : DecodeItemArgs) (returnAddress index : Z)
    (cursor endpoint acc : bv 64) :
  decodeItemDomainAt returnAddress decodeItemC1BDomain args ->
  endpoint = bv_add (Z_to_bv 64 (decodeItemInputPointer args)) (bv_add (bv_and (bv_add (bv_and (bv_sign_extend 64 (List.nth 0 (decodeItemInputBytes args) (BV 8 0))) (BV 64 255)) (BV 64 73)) (BV 64 255)) (BV 64 1)) ->
  0 <= index -> bv_unsigned cursor = decodeItemInputPointer args + 1 + index ->
  bv_unsigned cursor < bv_unsigned endpoint ->
  negb (bool_decide (bv_signed (bv_zero_extend 128 (bv_and (bv_add (bv_and (bv_sign_extend 64 (List.nth 0 (decodeItemInputBytes args) (BV 8 0))) (BV 64 255)) (BV 64 73)) (BV 64 255))) >=
    bv_signed (bv_zero_extend 128 (Z_to_bv 64 (decodeItemInputLength args))))) = true ->
  bool_decide (bv_signed (BV 128 183) < bv_signed (bv_zero_extend 128 (bv_and (bv_sign_extend 64 (List.nth 0 (decodeItemInputBytes args) (BV 8 0))) (BV 64 255)))) = true ->
  negb (bool_decide (bv_signed (bv_zero_extend 128 (bv_and (bv_sign_extend 64 (List.nth 0 (decodeItemInputBytes args) (BV 8 0))) (BV 64 255))) >= bv_signed (BV 128 192))) = true ->
  bv_unsigned acc = zesu_byte_window_fold (decodeItemInputBytes args) 1 (Z.to_nat index) ->
  bv_unsigned (bv_or (bv_shiftl acc (BV 64 8))
    (bv_zero_extend 64 (List.nth
      (Z.to_nat (bv_unsigned cursor - bv_unsigned (Z_to_bv 64 (decodeItemInputPointer args))))
      (decodeItemInputBytes args) (BV 8 0)))) =
    zesu_byte_window_fold (decodeItemInputBytes args) 1 (Z.to_nat (index + 1)).
Proof.
  intros Hdomain Hendpoint Hindex Horigin Hhead HcountGuard Hlower Hupper Hacc.
  eapply (loop_fold_step_from_complete_source_domain args returnAddress index cursor endpoint
    (Z_to_bv 64 (decodeItemInputLength args)) (bv_and (bv_add (bv_and (bv_sign_extend 64 (List.nth 0 (decodeItemInputBytes args) (BV 8 0))) (BV 64 255)) (BV 64 73)) (BV 64 255)) acc);
    [exact Hdomain | reflexivity | exact Hendpoint | exact Hindex | exact Horigin |
     exact Hhead | exact HcountGuard | | exact Hacc].
  exact (proj2 (loop_count_6a24 (List.nth 0 (decodeItemInputBytes args) (BV 8 0)) Hlower Hupper)).
Qed.

Lemma loop_fold_source_6ac4 (args : DecodeItemArgs) (returnAddress index : Z)
    (cursor endpoint acc : bv 64) :
  decodeItemDomainAt returnAddress decodeItemC1BDomain args ->
  endpoint = bv_add (Z_to_bv 64 (decodeItemInputPointer args)) (bv_add (bv_and (bv_add (bv_and (bv_sign_extend 64 (List.nth 0 (decodeItemInputBytes args) (BV 8 0))) (BV 64 255)) (BV 64 9)) (BV 64 255)) (BV 64 1)) ->
  0 <= index -> bv_unsigned cursor = decodeItemInputPointer args + 1 + index ->
  bv_unsigned cursor < bv_unsigned endpoint ->
  negb (bool_decide (bv_signed (bv_zero_extend 128 (bv_and (bv_add (bv_and (bv_sign_extend 64 (List.nth 0 (decodeItemInputBytes args) (BV 8 0))) (BV 64 255)) (BV 64 9)) (BV 64 255))) >=
    bv_signed (bv_zero_extend 128 (Z_to_bv 64 (decodeItemInputLength args))))) = true ->
  bool_decide (bv_signed (bv_zero_extend 128 (bv_and (bv_sign_extend 64 (List.nth 0 (decodeItemInputBytes args) (BV 8 0))) (BV 64 255))) >= bv_signed (BV 128 248)) = true ->
  bv_unsigned acc = zesu_byte_window_fold (decodeItemInputBytes args) 1 (Z.to_nat index) ->
  bv_unsigned (bv_or (bv_shiftl acc (BV 64 8))
    (bv_zero_extend 64 (List.nth
      (Z.to_nat (bv_unsigned cursor - bv_unsigned (Z_to_bv 64 (decodeItemInputPointer args))))
      (decodeItemInputBytes args) (BV 8 0)))) =
    zesu_byte_window_fold (decodeItemInputBytes args) 1 (Z.to_nat (index + 1)).
Proof.
  intros Hdomain Hendpoint Hindex Horigin Hhead HcountGuard Hlower Hacc.
  eapply (loop_fold_step_from_complete_source_domain args returnAddress index cursor endpoint
    (Z_to_bv 64 (decodeItemInputLength args)) (bv_and (bv_add (bv_and (bv_sign_extend 64 (List.nth 0 (decodeItemInputBytes args) (BV 8 0))) (BV 64 255)) (BV 64 9)) (BV 64 255)) acc);
    [exact Hdomain | reflexivity | exact Hendpoint | exact Hindex | exact Horigin |
     exact Hhead | exact HcountGuard | | exact Hacc].
  exact (proj2 (loop_count_6ac4 (List.nth 0 (decodeItemInputBytes args) (BV 8 0)) Hlower)).
Qed.
