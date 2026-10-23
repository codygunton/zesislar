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

Require Import ZesuSsz.Automation.SailEval.
Require Import ZesuSsz.Compliance.RlpInputBounds.
Require Import ZesuSsz.Contracts.RlpDecodeItem.
Require Import ZesuSsz.Compliance.ByteFold.
Import ListNotations.
Open Scope Z_scope.
#[local] Hint Unfold EvmSailRlp.evm_rlp.rlp_ref_hdr
  EvmSailRlp.evm_rlp.stateless_input_slice_byte
  EvmSailRlp.evm_rlp.stateless_input_byte_at
  EvmSailRlp.evm_rlp_types.returnM EvmSailRlp.evm_rlp_types.read_reg
  EvmSailRlp.evm_rlp.rlp_uint64_width
  EvmSailRlp.evm_rlp.stateless_input_sub_slice
  EvmSailRlp.evm_rlp.rlp_uint64_append bigEndian : sail.
#[local] Hint Rewrite shimInputLengthExact : zesu_sail.
#[local] Hint Unfold EvmSailRlp.evm_rlp._rec_rlp_uint64_width : zesu_sail_rec.

Lemma decodeItemRunPromptLongStringHeader prefix rest rs
    (slice : StatelessInputSliceFields 0 (Z.of_nat (List.length (prefix :: rest)))) :
  register_lookup shim_input_bytes rs = prefix :: rest ->
  StatelessInputSliceFields_len slice = Z.of_nat (List.length (prefix :: rest)) ->
  184 <= bv_unsigned prefix <= 191 ->
  1 + (bv_unsigned prefix - 183) <= Z.of_nat (List.length (prefix :: rest)) ->
  runPrompt (EvmSailRlp.evm_rlp.rlp_ref_hdr slice) rs true =
    (Success (false, Build_source_pointer (1 + (bv_unsigned prefix - 183)),
      bigEndian (firstn (Z.to_nat (bv_unsigned prefix - 183)) rest)), rs).
Proof. sail_eval. Qed.

Lemma decodeItemRunPromptLongListHeader prefix rest rs
    (slice : StatelessInputSliceFields 0 (Z.of_nat (List.length (prefix :: rest)))) :
  register_lookup shim_input_bytes rs = prefix :: rest ->
  StatelessInputSliceFields_len slice = Z.of_nat (List.length (prefix :: rest)) ->
  248 <= bv_unsigned prefix <= 255 ->
  1 + (bv_unsigned prefix - 247) <= Z.of_nat (List.length (prefix :: rest)) ->
  runPrompt (EvmSailRlp.evm_rlp.rlp_ref_hdr slice) rs true =
    (Success (true, Build_source_pointer (1 + (bv_unsigned prefix - 247)),
      bigEndian (firstn (Z.to_nat (bv_unsigned prefix - 247)) rest)), rs).
Proof. sail_eval. Qed.

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
Proof. sail_eval. Qed.

Lemma decodeItemRunPromptLongListHeaderRejected prefix rest rs
    (slice : StatelessInputSliceFields 0 (Z.of_nat (List.length (prefix :: rest)))) :
  register_lookup shim_input_bytes rs = prefix :: rest ->
  StatelessInputSliceFields_len slice = Z.of_nat (List.length (prefix :: rest)) ->
  248 <= bv_unsigned prefix <= 255 ->
  Z.of_nat (List.length (prefix :: rest)) < 1 + (bv_unsigned prefix - 247) ->
  runPrompt (EvmSailRlp.evm_rlp.rlp_ref_hdr slice) rs true = (Reject RlpDecode, rs).
Proof. sail_eval. Qed.

Print Assumptions decodeItemRunPromptLongStringHeaderRejected.
Print Assumptions decodeItemRunPromptLongListHeaderRejected.
