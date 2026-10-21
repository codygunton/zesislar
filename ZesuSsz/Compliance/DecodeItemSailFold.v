Require Import ZesuSsz.Automation.All.
From Coq Require Import List ZArith Lia.
From stdpp Require Import bitvector.definitions.
Require Import SailStdpp.Prompt_monad SailStdpp.Prompt.
Require Import EvmSailRlp.evm_rlp_types EvmSailRlp.evm_rlp.
Require Import ZesuSsz.Contracts.RlpDecodeItem.
Require Import ZesuSsz.Contracts.RlpDecodeItemContract.
Require Import ZesuSsz.Contracts.DecodeItemReturnFacts.
Require Import ZesuSsz.Compliance.ByteFold.
Require Import ZesuSsz.Proofs.DecodeItem.ByteFoldPure.
Require Import ZesuSsz.Compliance.SailRun.
Require Import ZesuSsz.Compliance.DecodeItemSailEvaluation.
Import ListNotations.
Open Scope Z_scope.
Open Scope list_scope.

Lemma decodeItemRunPromptLengthFold prefix rest rs len count width fuel
    (slice : StatelessInputSliceFields 1 len)
    (access : Acc (Zwf 0) fuel) :
  width = Z.of_nat count -> fuel = width ->
  register_lookup shim_input_bytes rs = prefix :: rest ->
  width <= len -> len <= Z.of_nat (List.length rest) ->
  runPrompt (EvmSailRlp.evm_rlp._rec_rlp_uint64_width slice
    width fuel access) rs true =
    (Success (bigEndian (firstn count rest)), rs).
Proof.
  revert width fuel access. induction count as [|count IH];
    intros width fuel access Hcount Hfuel Hbytes Hwidth Hlen; subst width; subst fuel.
  - destruct access. reflexivity.
  - destruct access as [access].
    destruct (nth_error rest count) as [next|] eqn:Hnext.
    2: { apply nth_error_None in Hnext. lia. }
    cbn [EvmSailRlp.evm_rlp._rec_rlp_uint64_width].
    replace (Z.of_nat (S count) - 1) with (Z.of_nat count) by lia.
    erewrite decodeItemRunPromptBindSuccess with
      (value := bigEndian (firstn count rest)) (rs' := rs).
    2: { eapply IH; eauto; lia. }
    erewrite decodeItemRunPromptBindSuccess with (value := next) (rs' := rs).
    2: {
      apply decodeItemRunPromptSliceByte with (bytes := prefix :: rest);
        try exact Hbytes; try (simpl; lia).
      replace (Z.to_nat (1 + (Z.of_nat (S count) - 1))) with (S count) by lia.
      exact Hnext.
    }
    unfold EvmSailRlp.evm_rlp.rlp_uint64_append.
    rewrite decodeItemUintByte.
    rewrite (decodeItem_firstn_snoc rest count next Hnext).
    rewrite zesu_bigEndian_snoc.
    cbn [EvmSailRlp.evm_rlp_types.returnM SailStdpp.Prompt_monad.returnm runPrompt].
    rewrite (Z.mul_comm (bigEndian (firstn count rest)) 256). reflexivity.
Qed.

Print Assumptions decodeItemRunPromptLengthFold.

Local Ltac decodeItemLongHeader prefix rest rs :=
  intros Hbytes Hlength Hclass Hbound;
  unfold EvmSailRlp.evm_rlp.rlp_ref_hdr; rewrite Hlength;
  cbn [SailStdpp.Prompt_monad.bind0 EvmSailRlp.evm_rlp_types.returnM
    SailStdpp.Prompt_monad.returnm SailStdpp.Prompt_monad.bind];
  first [lazymatch goal with
    | |- _ = (Success (?kind, Build_source_pointer ?header, ?payload), _) =>
      erewrite decodeItemRunPromptBindSuccess with
        (value := (kind, header, payload)) (rs' := rs); [reflexivity|]
    end | apply decodeItemRunPromptBindReject];
  erewrite decodeItemRunPromptBindSuccess with (value := prefix) (rs' := rs);
  [|apply decodeItemRunPromptHeadByte; exact Hbytes];
  rewrite decodeItemUintByte;
  repeat match goal with
  | |- context [Z.ltb ?x ?y] =>
    first [rewrite (proj2 (Z.ltb_lt x y) ltac:(lia))
          |rewrite (proj2 (Z.ltb_ge x y) ltac:(lia))]
  | |- context [Z.leb ?x ?y] =>
    first [rewrite (proj2 (Z.leb_le x y) ltac:(lia))
          |rewrite (proj2 (Z.leb_gt x y) ltac:(lia))]
  end;
  first [reflexivity|
    lazymatch goal with
    | |- _ = (Success (_, _, ?payload), _) =>
      erewrite decodeItemRunPromptBindSuccess with
        (value := payload) (rs' := rs); [reflexivity|]
    end;
    unfold EvmSailRlp.evm_rlp.rlp_uint64_width;
    eapply decodeItemRunPromptLengthFold; try exact Hbytes;
      try reflexivity; try (rewrite Z2Nat.id; lia);
    cbn [List.length] in Hbound; rewrite Nat2Z.inj_succ in Hbound; lia].

Lemma decodeItemRunPromptLongStringHeader prefix rest rs
    (slice : StatelessInputSliceFields 0 (Z.of_nat (List.length (prefix :: rest)))) :
  register_lookup shim_input_bytes rs = prefix :: rest ->
  StatelessInputSliceFields_len slice = Z.of_nat (List.length (prefix :: rest)) ->
  184 <= bv_unsigned prefix <= 191 ->
  1 + (bv_unsigned prefix - 183) <= Z.of_nat (List.length (prefix :: rest)) ->
  runPrompt (EvmSailRlp.evm_rlp.rlp_ref_hdr slice) rs true =
    (Success (false, Build_source_pointer (1 + (bv_unsigned prefix - 183)),
      bigEndian (firstn (Z.to_nat (bv_unsigned prefix - 183)) rest)), rs).
Proof. decodeItemLongHeader prefix rest rs. Qed.

Lemma decodeItemRunPromptLongListHeader prefix rest rs
    (slice : StatelessInputSliceFields 0 (Z.of_nat (List.length (prefix :: rest)))) :
  register_lookup shim_input_bytes rs = prefix :: rest ->
  StatelessInputSliceFields_len slice = Z.of_nat (List.length (prefix :: rest)) ->
  248 <= bv_unsigned prefix <= 255 ->
  1 + (bv_unsigned prefix - 247) <= Z.of_nat (List.length (prefix :: rest)) ->
  runPrompt (EvmSailRlp.evm_rlp.rlp_ref_hdr slice) rs true =
    (Success (true, Build_source_pointer (1 + (bv_unsigned prefix - 247)),
      bigEndian (firstn (Z.to_nat (bv_unsigned prefix - 247)) rest)), rs).
Proof. decodeItemLongHeader prefix rest rs. Qed.

Print Assumptions decodeItemRunPromptLongStringHeader.
Print Assumptions decodeItemRunPromptLongListHeader.

Lemma decodeItemBigEndianNonnegative bytes : 0 <= bigEndian bytes.
Proof.
  unfold bigEndian.
  assert (Hfold : forall (input : list byte) accumulator,
    0 <= accumulator ->
    0 <= fold_left (fun acc value => 256 * acc + bv_unsigned value) input accumulator).
  {
    induction input as [|head tail IH]; intros accumulator Hacc;
      cbn [fold_left]; first exact Hacc.
    apply IH. pose proof (bv_unsigned_in_range _ head). lia.
  }
  apply Hfold. lia.
Qed.

Lemma decodeItemRunPromptLongHeader args isList prefix rest n payloadStart lengthBytes :
  decodeItemFoldProvenance args isList prefix rest n payloadStart lengthBytes ->
  1 + n <= Z.of_nat (List.length (decodeItemInputBytes args)) ->
  runPrompt (EvmSailRlp.evm_rlp.rlp_ref_hdr (decodeItemSailCursor args))
    (decodeItemInstalledState (decodeItemInputBytes args)) true =
    (Success (isList, Build_source_pointer (1 + n), bigEndian lengthBytes),
      decodeItemInstalledState (decodeItemInputBytes args)).
Proof.
  intros (Hinput & Hclass & Hn & Hstart & Hbytes) Hfits.
  unfold decodeItemInputHead in Hinput.
  rewrite Hn. rewrite Hbytes. rewrite Hn in Hfits.
  unfold decodeItemSailCursor. rewrite Hinput. rewrite Hinput in Hfits.
  rewrite Hn.
  destruct isList.
  - apply decodeItemRunPromptLongListHeader; try reflexivity;
      auto using decodeItemInstalledBytes.
  - apply decodeItemRunPromptLongStringHeader; try reflexivity;
      auto using decodeItemInstalledBytes.
Qed.

Print Assumptions decodeItemBigEndianNonnegative.
Print Assumptions decodeItemRunPromptLongHeader.

Lemma decodeItemRunPromptLongStringHeaderRejected prefix rest rs
    (slice : StatelessInputSliceFields 0 (Z.of_nat (List.length (prefix :: rest)))) :
  register_lookup shim_input_bytes rs = prefix :: rest ->
  StatelessInputSliceFields_len slice = Z.of_nat (List.length (prefix :: rest)) ->
  184 <= bv_unsigned prefix <= 191 ->
  Z.of_nat (List.length (prefix :: rest)) < 1 + (bv_unsigned prefix - 183) ->
  runPrompt (EvmSailRlp.evm_rlp.rlp_ref_hdr slice) rs true = (Reject RlpDecode, rs).
Proof. decodeItemLongHeader prefix rest rs. Qed.

Lemma decodeItemRunPromptLongListHeaderRejected prefix rest rs
    (slice : StatelessInputSliceFields 0 (Z.of_nat (List.length (prefix :: rest)))) :
  register_lookup shim_input_bytes rs = prefix :: rest ->
  StatelessInputSliceFields_len slice = Z.of_nat (List.length (prefix :: rest)) ->
  248 <= bv_unsigned prefix <= 255 ->
  Z.of_nat (List.length (prefix :: rest)) < 1 + (bv_unsigned prefix - 247) ->
  runPrompt (EvmSailRlp.evm_rlp.rlp_ref_hdr slice) rs true = (Reject RlpDecode, rs).
Proof. decodeItemLongHeader prefix rest rs. Qed.

Print Assumptions decodeItemRunPromptLongStringHeaderRejected.
Print Assumptions decodeItemRunPromptLongListHeaderRejected.
