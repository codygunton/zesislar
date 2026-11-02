Require Import ZesuSsz.Automation.All.
Require Import ZesuSsz.Automation.ByteWindowFold.
Require Import ZesuSsz.Automation.ByteWindowFoldIteration.
Require Import ZesuSsz.Contracts.RlpDecodeItemContract.
Require Import ZesuSsz.Evidence.LoopSourceReadControls.
Require Import ZesuSsz.Evidence.LoopSourceIndexControls.
Require Import ZesuSsz.Evidence.LoopFoldCountControls.
From Coq Require Import Lists.List ZArith.ZArith Lia Bool.Bool.
From stdpp Require Import bitvector.definitions decidable.
Open Scope Z_scope.

Lemma loop_fold_iterations_from_complete_source_domain (args : DecodeItemArgs) (returnAddress index : Z)
    (cursor endpoint length_word count : bv 64) :
  decodeItemDomainAt returnAddress decodeItemC1BDomain args ->
  length_word = Z_to_bv 64 (decodeItemInputLength args) ->
  endpoint = bv_add (Z_to_bv 64 (decodeItemInputPointer args)) (bv_add count (BV 64 1)) ->
  0 <= index -> bv_unsigned cursor = decodeItemInputPointer args + 1 + index ->
  bv_unsigned cursor < bv_unsigned endpoint ->
  negb (bool_decide (bv_signed (bv_zero_extend 128 count) >=
                    bv_signed (bv_zero_extend 128 length_word))) = true ->
  bv_unsigned count <= 8 ->
  index = bv_unsigned cursor - (decodeItemInputPointer args + 1) /\
  bv_unsigned (zesu_byte_window_iterate64 (decodeItemInputBytes args) 1 (Z.to_nat index)) =
    zesu_byte_window_fold (decodeItemInputBytes args) 1 (Z.to_nat index).
Proof.
  intros Hdomain HlengthWord Hendpoint Hindex Horigin Hhead HcountGuard Hwidth.
  pose proof (loop_index_from_complete_source_domain args returnAddress index cursor endpoint
    length_word count Hdomain HlengthWord Hendpoint Hindex Horigin Hhead HcountGuard) as HindexCount.
  pose proof (loop_read_from_complete_source_domain args returnAddress index cursor endpoint
    length_word count Hdomain HlengthWord Hendpoint Hindex Horigin Hhead HcountGuard)
    as [Hrange Hlookup].
  split.
  { lia. }
  apply zesu_byte_window_iterate_unsigned.
  { apply Nat2Z.inj_le. rewrite Z2Nat.id by exact Hindex. simpl. lia. }
  { apply Nat2Z.inj_le. rewrite Nat2Z.inj_add.
    rewrite Z2Nat.id by exact Hindex. simpl. lia. }
Qed.

Lemma loop_fold_iterations_6a24 (args : DecodeItemArgs) (returnAddress index : Z)
    (cursor endpoint : bv 64) :
  decodeItemDomainAt returnAddress decodeItemC1BDomain args ->
  endpoint = bv_add (Z_to_bv 64 (decodeItemInputPointer args)) (bv_add (bv_and (bv_add (bv_and (bv_sign_extend 64 (List.nth 0 (decodeItemInputBytes args) (BV 8 0))) (BV 64 255)) (BV 64 73)) (BV 64 255)) (BV 64 1)) ->
  0 <= index -> bv_unsigned cursor = decodeItemInputPointer args + 1 + index ->
  bv_unsigned cursor < bv_unsigned endpoint ->
  negb (bool_decide (bv_signed (bv_zero_extend 128 (bv_and (bv_add (bv_and (bv_sign_extend 64 (List.nth 0 (decodeItemInputBytes args) (BV 8 0))) (BV 64 255)) (BV 64 73)) (BV 64 255))) >=
    bv_signed (bv_zero_extend 128 (Z_to_bv 64 (decodeItemInputLength args))))) = true ->
  bool_decide (bv_signed (BV 128 183) < bv_signed (bv_zero_extend 128 (bv_and (bv_sign_extend 64 (List.nth 0 (decodeItemInputBytes args) (BV 8 0))) (BV 64 255)))) = true ->
  negb (bool_decide (bv_signed (bv_zero_extend 128 (bv_and (bv_sign_extend 64 (List.nth 0 (decodeItemInputBytes args) (BV 8 0))) (BV 64 255))) >= bv_signed (BV 128 192))) = true ->
  index = bv_unsigned cursor - (decodeItemInputPointer args + 1) /\
  bv_unsigned (zesu_byte_window_iterate64 (decodeItemInputBytes args) 1 (Z.to_nat index)) =
    zesu_byte_window_fold (decodeItemInputBytes args) 1 (Z.to_nat index).
Proof.

  intros Hdomain Hendpoint Hindex Horigin Hhead HcountGuard Hlower Hupper .
  eapply (loop_fold_iterations_from_complete_source_domain args returnAddress index cursor endpoint
    (Z_to_bv 64 (decodeItemInputLength args)) (bv_and (bv_add (bv_and (bv_sign_extend 64 (List.nth 0 (decodeItemInputBytes args) (BV 8 0))) (BV 64 255)) (BV 64 73)) (BV 64 255)));
    [exact Hdomain | reflexivity | exact Hendpoint | exact Hindex | exact Horigin |
     exact Hhead | exact HcountGuard | ].
  exact (proj2 (loop_count_6a24 (List.nth 0 (decodeItemInputBytes args) (BV 8 0)) Hlower Hupper)).
Qed.

Lemma loop_fold_iterations_6ac4 (args : DecodeItemArgs) (returnAddress index : Z)
    (cursor endpoint : bv 64) :
  decodeItemDomainAt returnAddress decodeItemC1BDomain args ->
  endpoint = bv_add (Z_to_bv 64 (decodeItemInputPointer args)) (bv_add (bv_and (bv_add (bv_and (bv_sign_extend 64 (List.nth 0 (decodeItemInputBytes args) (BV 8 0))) (BV 64 255)) (BV 64 9)) (BV 64 255)) (BV 64 1)) ->
  0 <= index -> bv_unsigned cursor = decodeItemInputPointer args + 1 + index ->
  bv_unsigned cursor < bv_unsigned endpoint ->
  negb (bool_decide (bv_signed (bv_zero_extend 128 (bv_and (bv_add (bv_and (bv_sign_extend 64 (List.nth 0 (decodeItemInputBytes args) (BV 8 0))) (BV 64 255)) (BV 64 9)) (BV 64 255))) >=
    bv_signed (bv_zero_extend 128 (Z_to_bv 64 (decodeItemInputLength args))))) = true ->
  bool_decide (bv_signed (bv_zero_extend 128 (bv_and (bv_sign_extend 64 (List.nth 0 (decodeItemInputBytes args) (BV 8 0))) (BV 64 255))) >= bv_signed (BV 128 248)) = true ->
  index = bv_unsigned cursor - (decodeItemInputPointer args + 1) /\
  bv_unsigned (zesu_byte_window_iterate64 (decodeItemInputBytes args) 1 (Z.to_nat index)) =
    zesu_byte_window_fold (decodeItemInputBytes args) 1 (Z.to_nat index).
Proof.

  intros Hdomain Hendpoint Hindex Horigin Hhead HcountGuard Hlower .
  eapply (loop_fold_iterations_from_complete_source_domain args returnAddress index cursor endpoint
    (Z_to_bv 64 (decodeItemInputLength args)) (bv_and (bv_add (bv_and (bv_sign_extend 64 (List.nth 0 (decodeItemInputBytes args) (BV 8 0))) (BV 64 255)) (BV 64 9)) (BV 64 255)));
    [exact Hdomain | reflexivity | exact Hendpoint | exact Hindex | exact Horigin |
     exact Hhead | exact HcountGuard | ].
  exact (proj2 (loop_count_6ac4 (List.nth 0 (decodeItemInputBytes args) (BV 8 0)) Hlower)).
Qed.
