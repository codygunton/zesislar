Require Import ZesuSsz.Automation.All.
Require Import ZesuSsz.Automation.SailEval.
From Coq Require Import Bool List String ZArith Lia.
Require Import SailStdpp.MachineWord SailStdpp.Prompt_monad.
Require Import SailStdpp.Prompt.
Require Import SailStdpp.Operators_mwords.
From stdpp Require Import bitvector.definitions.
Require Import EvmSailRlp.evm_rlp_types EvmSailRlp.evm_rlp.
Require Import ZesuSsz.Compliance.SailRun.
Require Import ZesuSsz.Compliance.RlpInputBounds.
Require Import ZesuSsz.Contracts.RlpDecodeItem.
Require Import ZesuSsz.Contracts.RlpDecodeItemContract.
Require Import ZesuMachineMap.Machine.
Require Import ZesuSsz.Compliance.DecodeItemSemanticIntroduction.
Import ListNotations.
Open Scope string_scope.
Open Scope Z_scope.

#[local] Hint Unfold EvmSailRlp.evm_rlp.rlp_ref_hdr
  EvmSailRlp.evm_rlp.rlp_decode_item
  EvmSailRlp.evm_rlp.stateless_input_slice_byte
  EvmSailRlp.evm_rlp.stateless_input_byte_at
  EvmSailRlp.evm_rlp_types.returnM EvmSailRlp.evm_rlp_types.read_reg : sail.
#[local] Hint Rewrite shimInputLengthExact : zesu_sail.

Lemma decodeItemRunPromptBindSuccess {A B} (action : M A) (next : A -> M B)
    rs value rs' :
  runPrompt action rs true = (Success value, rs') ->
  runPrompt (SailStdpp.Prompt_monad.bind action next) rs true =
    runPrompt (next value) rs' true.
Proof.
  intros Hrun. etransitivity; [apply sail_run_bind |].
  rewrite Hrun. reflexivity.
Qed.

Print Assumptions decodeItemRunPromptBindSuccess.

Lemma decodeItemRunPromptHeadByte prefix rest rs
    (slice : StatelessInputSliceFields 0 (Z.of_nat (List.length (prefix :: rest)))) :
  register_lookup shim_input_bytes rs = prefix :: rest ->
  runPrompt (EvmSailRlp.evm_rlp.stateless_input_slice_byte slice 0) rs true =
    (Success prefix, rs).
Proof. sail_eval. Qed.

Print Assumptions decodeItemRunPromptHeadByte.

Lemma decodeItemUintByte (value : byte) : uint value = bv_unsigned value.
Proof. apply sail_uint_unsigned. Qed.

Lemma decodeItemRunPromptLiteralHeader prefix rest rs
    (slice : StatelessInputSliceFields 0 (Z.of_nat (List.length (prefix :: rest)))) :
  register_lookup shim_input_bytes rs = prefix :: rest ->
  StatelessInputSliceFields_len slice = Z.of_nat (List.length (prefix :: rest)) ->
  bv_unsigned prefix <= 127 ->
  runPrompt (EvmSailRlp.evm_rlp.rlp_ref_hdr slice) rs true =
    (Success (false, Build_source_pointer 0, 1), rs).
Proof. sail_eval. Qed.

Print Assumptions decodeItemUintByte.
Print Assumptions decodeItemRunPromptLiteralHeader.

Lemma decodeItemRunPromptShortStringHeader prefix rest rs
    (slice : StatelessInputSliceFields 0 (Z.of_nat (List.length (prefix :: rest)))) :
  register_lookup shim_input_bytes rs = prefix :: rest ->
  StatelessInputSliceFields_len slice = Z.of_nat (List.length (prefix :: rest)) ->
  128 <= bv_unsigned prefix <= 183 ->
  runPrompt (EvmSailRlp.evm_rlp.rlp_ref_hdr slice) rs true =
    (Success (false, Build_source_pointer 1, bv_unsigned prefix - 128), rs).
Proof. sail_eval. Qed.

Lemma decodeItemRunPromptShortListHeader prefix rest rs
    (slice : StatelessInputSliceFields 0 (Z.of_nat (List.length (prefix :: rest)))) :
  register_lookup shim_input_bytes rs = prefix :: rest ->
  StatelessInputSliceFields_len slice = Z.of_nat (List.length (prefix :: rest)) ->
  192 <= bv_unsigned prefix <= 247 ->
  runPrompt (EvmSailRlp.evm_rlp.rlp_ref_hdr slice) rs true =
    (Success (true, Build_source_pointer 1, bv_unsigned prefix - 192), rs).
Proof. sail_eval. Qed.

Definition decodeItemInstalledState bytes : regstate :=
  register_set shim_input_bytes bytes
    (register_set k_execution_profile EvmSailRlp.evm_rlp.DEFAULT_EXECUTION_PROFILE
      (register_set shim_input_bytes [] init_regstate)).

Lemma decodeItemRunPromptInitialized bytes :
  runPrompt (initializedInput bytes) init_regstate true =
    (Success tt, decodeItemInstalledState bytes).
Proof.
  reflexivity.
Qed.

Lemma decodeItemInstalledBytes bytes :
  register_lookup shim_input_bytes (decodeItemInstalledState bytes) = bytes.
Proof.
  unfold decodeItemInstalledState. apply register_lookup_set.
Qed.

Print Assumptions decodeItemRunPromptShortStringHeader.
Print Assumptions decodeItemRunPromptShortListHeader.
Print Assumptions decodeItemRunPromptInitialized.
Print Assumptions decodeItemInstalledBytes.

Lemma decodeItemRunPromptAcceptedHeader (prefix : byte) (rest : list byte)
    rs isList headerLength payloadLength
    (slice : StatelessInputSliceFields 0 (Z.of_nat (List.length (prefix :: rest)))) :
  StatelessInputSliceFields_len slice = Z.of_nat (List.length (prefix :: rest)) ->
  runPrompt (EvmSailRlp.evm_rlp.rlp_ref_hdr slice) rs true =
    (Success (isList, Build_source_pointer headerLength, payloadLength), rs) ->
  0 <= headerLength -> 0 <= payloadLength ->
  0 < headerLength + payloadLength ->
  headerLength + payloadLength <= Z.of_nat (List.length (prefix :: rest)) ->
  exists fullLength contentLength (field : RlpFieldRef 0 fullLength contentLength),
    runPrompt (EvmSailRlp.evm_rlp.rlp_decode_item slice) rs true =
      (Success (@existT Z (fun full => {content : Z & RlpFieldRef 0 full content})
        fullLength (@existT Z (fun content => RlpFieldRef 0 fullLength content)
          contentLength field)), rs) /\
    RlpFieldRef_is_list field = isList /\
    fullLength - contentLength = headerLength /\ contentLength = payloadLength.
Proof.
  intros Hlength Hheader Hnonnegative Hpayload Hpositive Hfits.
  exists (headerLength + payloadLength), payloadLength. eexists. split.
  - unfold EvmSailRlp.evm_rlp.rlp_decode_item.
    cbn [SailStdpp.Prompt_monad.bind0 EvmSailRlp.evm_rlp_types.returnM
      SailStdpp.Prompt_monad.returnm SailStdpp.Prompt_monad.bind].
    erewrite decodeItemRunPromptBindSuccess with
      (value := (isList, headerLength, payloadLength)) (rs' := rs).
    + rewrite (proj2 (Z.ltb_ge (Z.of_nat (List.length (prefix :: rest))) headerLength) ltac:(lia)).
      rewrite (proj2 (Z.ltb_ge (Z.of_nat (List.length (prefix :: rest)) - headerLength) payloadLength) ltac:(lia)).
      rewrite (proj2 (Z.ltb_lt 0 (headerLength + payloadLength)) Hpositive).
      rewrite (proj2 (Z.leb_le _ _) Hfits). reflexivity.
    + erewrite decodeItemRunPromptBindSuccess with
        (value := (isList, Build_source_pointer headerLength, payloadLength))
        (rs' := rs); last exact Hheader.
      reflexivity.
  - simpl. repeat split; lia.
Qed.

Print Assumptions decodeItemRunPromptAcceptedHeader.

Lemma decodeItemSailInputLengthBound args :
  decodeItemC1BDomain args ->
  Z.of_nat (List.length (decodeItemInputBytes args)) <= stateless_input_region_bound.
Proof.
  intros Hdomain.
  pose proof (decodeItemDomainInputLengthBounds args Hdomain) as Hbound.
  destruct Hdomain as [Hlength _].
  rewrite <- Hlength. unfold stateless_input_region_bound. lia.
Qed.

Lemma decodeItemSailInputSliceValid args :
  decodeItemC1BDomain args ->
  validInputSlice (decodeItemInputBytes args) 0
    (Z.of_nat (List.length (decodeItemInputBytes args))) = true.
Proof.
  intros Hdomain. pose proof (decodeItemSailInputLengthBound args Hdomain) as Hbound.
  unfold validInputSlice. simpl.
  rewrite (proj2 (Z.leb_le 0 _) (Nat2Z.is_nonneg _)).
  rewrite (proj2 (Z.leb_le _ _) Hbound). rewrite Z.leb_refl. reflexivity.
Qed.

Print Assumptions decodeItemSailInputLengthBound.
Print Assumptions decodeItemSailInputSliceValid.

Lemma decodeItemRunPromptShimByte bytes index value rs :
  nth_error bytes index = Some value ->
  runPrompt (EvmSailRlp.evm_rlp.shim_byte_at bytes (Z.of_nat index)) rs true =
    (Success value, rs).
Proof. apply sail_run_shim_byte_nat. Qed.

Lemma decodeItemRunPromptSliceByte bytes base len off value rs
    (slice : StatelessInputSliceFields base len) :
  register_lookup shim_input_bytes rs = bytes ->
  0 <= base -> 0 <= len -> base + len <= Z.of_nat (List.length bytes) ->
  0 <= off < len -> nth_error bytes (Z.to_nat (base + off)) = Some value ->
  runPrompt (EvmSailRlp.evm_rlp.stateless_input_slice_byte slice off) rs true =
    (Success value, rs).
Proof. sail_eval. eapply sail_run_shim_byte; [lia | eassumption]. Qed.

Print Assumptions decodeItemRunPromptShimByte.
Print Assumptions decodeItemRunPromptSliceByte.

Lemma decodeItemRunPromptRejectedHeader (prefix : byte) (rest : list byte)
    rs isList headerLength payloadLength
    (slice : StatelessInputSliceFields 0 (Z.of_nat (List.length (prefix :: rest)))) :
  runPrompt (EvmSailRlp.evm_rlp.rlp_ref_hdr slice) rs true =
    (Success (isList, Build_source_pointer headerLength, payloadLength), rs) ->
  Z.of_nat (List.length (prefix :: rest)) < headerLength + payloadLength ->
  runPrompt (EvmSailRlp.evm_rlp.rlp_decode_item slice) rs true = (Reject RlpDecode, rs).
Proof.
  intros Hheader Hreject.
  unfold EvmSailRlp.evm_rlp.rlp_decode_item.
  cbn [SailStdpp.Prompt_monad.bind0 EvmSailRlp.evm_rlp_types.returnM
    SailStdpp.Prompt_monad.returnm SailStdpp.Prompt_monad.bind].
  erewrite decodeItemRunPromptBindSuccess with
    (value := (isList, headerLength, payloadLength)) (rs' := rs).
  - destruct (Z.of_nat (List.length (prefix :: rest)) <? headerLength) eqn:Hguard.
    + reflexivity.
    + apply Z.ltb_ge in Hguard.
      rewrite (proj2 (Z.ltb_lt
        (Z.of_nat (List.length (prefix :: rest)) - headerLength) payloadLength) ltac:(lia)).
      reflexivity.
  - erewrite decodeItemRunPromptBindSuccess with
      (value := (isList, Build_source_pointer headerLength, payloadLength))
      (rs' := rs); last exact Hheader.
    reflexivity.
Qed.

Print Assumptions decodeItemRunPromptRejectedHeader.

Lemma decodeItemRunPromptBindReject {A B} (action : M A) (next : A -> M B)
    rs reason rs' :
  runPrompt action rs true = (Reject reason, rs') ->
  runPrompt (SailStdpp.Prompt_monad.bind action next) rs true = (Reject reason, rs').
Proof. intros Hrun. rewrite sail_run_bind. rewrite Hrun. reflexivity. Qed.

Print Assumptions decodeItemRunPromptBindReject.

Lemma decodeItemRunPromptHeaderReject (prefix : byte) (rest : list byte)
    rs (slice : StatelessInputSliceFields 0 (Z.of_nat (List.length (prefix :: rest)))) :
  runPrompt (EvmSailRlp.evm_rlp.rlp_ref_hdr slice) rs true = (Reject RlpDecode, rs) ->
  runPrompt (EvmSailRlp.evm_rlp.rlp_decode_item slice) rs true = (Reject RlpDecode, rs).
Proof.
  intros Hheader.
  unfold EvmSailRlp.evm_rlp.rlp_decode_item.
  cbn [SailStdpp.Prompt_monad.bind0 EvmSailRlp.evm_rlp_types.returnM
    SailStdpp.Prompt_monad.returnm SailStdpp.Prompt_monad.bind].
  rewrite (proj2 (Z.eqb_neq (Z.of_nat (List.length (prefix :: rest))) 0)
    ltac:(cbn [List.length]; rewrite Nat2Z.inj_succ; lia)).
  cbn [SailStdpp.Prompt_monad.bind0 EvmSailRlp.evm_rlp_types.returnM SailStdpp.Prompt_monad.returnm
    SailStdpp.Prompt_monad.bind].
  apply decodeItemRunPromptBindReject.
  apply decodeItemRunPromptBindReject. exact Hheader.
Qed.

Print Assumptions decodeItemRunPromptHeaderReject.
