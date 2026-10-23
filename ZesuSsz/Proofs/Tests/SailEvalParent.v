Require Import ZesuSsz.Automation.All.
From Coq Require Import Bool List String ZArith Lia.
Require Import SailStdpp.MachineWord SailStdpp.Values SailStdpp.Prompt_monad.
Require Import SailStdpp.Prompt SailStdpp.Operators_mwords.
From stdpp Require Import bitvector.definitions.
Require Import EvmSailRlp.evm_rlp_types.
Require Import ZesuSsz.Compliance.SailRun.
Import ListNotations.
Open Scope Z_scope.

(* Importing the evaluator must preserve the model and client hints. *)
Definition sail_import_sentinel : Z := 29.
#[local] Hint Unfold sail_import_sentinel : sail.
Lemma sail_import_model_before : ssz_uint_bound = (2 ^ 64 - 1)%Z.
Proof. autounfold_one with sail. reflexivity. Qed.
Lemma sail_import_client_before : sail_import_sentinel = 29%Z.
Proof. autounfold_one with sail. reflexivity. Qed.

Require Import ZesuSsz.Automation.SailEval.
Require Import ZesuSsz.Automation.SailBytes ZesuSsz.Compliance.EvmSailHashBytes.

Lemma sail_import_model_after : ssz_uint_bound = (2 ^ 64 - 1)%Z.
Proof. autounfold_one with sail. reflexivity. Qed.
Lemma sail_import_client_after : sail_import_sentinel = 29%Z.
Proof. autounfold_one with sail. reflexivity. Qed.
Print Assumptions sail_import_model_before.
Print Assumptions sail_import_client_before.
Print Assumptions sail_import_model_after.
Print Assumptions sail_import_client_after.

Require Import EvmSailRlp.evm_rlp.
Require Import ZesuSsz.Compliance.RlpInputBounds.
Import ListNotations.
Open Scope Z_scope.
#[local] Hint Unfold EvmSailRlp.evm_rlp.rlp_ref_hdr
  EvmSailRlp.evm_rlp.stateless_input_slice_byte
  EvmSailRlp.evm_rlp.stateless_input_byte_at
  EvmSailRlp.evm_rlp_types.returnM EvmSailRlp.evm_rlp_types.read_reg
  EvmSailRlp.evm_rlp.stateless_input_sub_slice
  : sail.
#[local] Hint Rewrite shimInputLengthExact : zesu_sail.

Ltac sail_parent_primitive :=
  first
    [ sail_closed_arith
    | progress (autorewrite with zesu_sail)
    | progress (cbn [List.length] in *)
    | progress (cbn [SailStdpp.Prompt_monad.bind0
        SailStdpp.Prompt_monad.bind SailStdpp.Prompt_monad.returnm
        SailStdpp.Prompt_monad.read_reg SailStdpp.Prompt.and_boolM
        assert_exp' runPrompt List.length andb List.firstn List.fold_left
        EvmSailRlp.evm_rlp.shim_byte_at
        stateless_input_length_value StatelessInputSliceFields_len])
    | sail_closed_arith
    | sail_context_rewrite
    | progress (autorewrite with zesu_sail)
    | progress (autounfold_one with sail)
    | sail_guard
    ].

#[local] Hint Rewrite @sail_get_slice_int using lia : zesu_sail.
#[local] Hint Unfold EvmSailRlp.evm_rlp.decode_parent_header_fields
  EvmSailRlp.evm_rlp.rlp_decode_item EvmSailRlp.evm_rlp.shim_load_n : sail.
Local Opaque EvmSailRlp.evm_rlp._rec_shim_load_n.


Lemma sail_word_from_bits_small value :
  0 <= value < 2 ^ 256 ->
  word_from_bits (Z_to_bv 256 value) = Build_word value.
Proof.
  intros Hbound. unfold word_from_bits, u256.
  rewrite sail_uint_unsigned. cbn [word_value].
  rewrite Z_to_bv_unsigned. unfold bv_wrap, bv_modulus.
  rewrite Z.mod_small by exact Hbound. reflexivity.
Qed.
Lemma sail_parent_symbolic_first rs (fields : ParentHeaderFields)
    (slice : StatelessInputSliceFields 0 33)
    (h : list byte) (Hhash : length h = 32%nat) :
  register_lookup shim_input_bytes rs =
    (Z_to_bv 8 160 :: h) ->
  StatelessInputSliceFields_len slice = 33 ->
  runPrompt (EvmSailRlp.evm_rlp.decode_parent_header_fields slice
    (Build_parent_header_field_cursor 0) fields) rs true =
  (Success (Build_ParentHeaderFields
    (word_to_hash (Build_word
      (fold_left (fun accumulator (item : byte) =>
        Z.add (Z.mul accumulator 256) (@uint 8 item)) h 0)))
    (ParentHeaderFields_state_root fields)
    (ParentHeaderFields_base_fee fields)
    (ParentHeaderFields_blob_gas_used fields)
    (ParentHeaderFields_excess_blob_gas fields)
    true (ParentHeaderFields_have_state fields)
    (ParentHeaderFields_have_base_fee fields)
    (ParentHeaderFields_have_blob_gas fields)
    (ParentHeaderFields_have_excess_blob_gas fields)), rs).
Proof.
intros Hbytes Hlength. unfold EvmSailRlp.evm_rlp.decode_parent_header_fields. cbn [parent_header_field_cursor_value]. rewrite Hlength.
sail_generated_step.
cbn [parent_header_field_cursor_value].
repeat sail_closed_arith.
rewrite sail_run_bind.
cbn [assert_exp' runPrompt SailStdpp.Prompt_monad.bind returnM].
repeat first [sail_load_summary | sail_parent_primitive].
cbn [List.skipn].
rewrite skipn_O.
rewrite firstn_all2 by lia.
rewrite Z.shiftr_0_r.
pose proof (sail_fold_uint_bound h) as Hfold. rewrite Hhash in Hfold. change (0 <= fold_left (fun accumulator (item : byte) => Z.add (Z.mul accumulator 256) (@uint 8 item)) h 0 < 2 ^ 256) in Hfold.
rewrite sail_word_from_bits_small by exact Hfold.
cbn [word_value].
destruct fields; reflexivity.
Qed.
Print Assumptions sail_parent_symbolic_first.

Lemma sail_parent_first_cursor_end (slice : StatelessInputSliceFields 0 33)
    (h : list byte) :
  length h = 32%nat ->
  let field : RlpFieldRef 0 33 32 :=
    {| RlpFieldRef_source := TypeCasts.autocast
         (stateless_input_sub_slice slice 0 33);
       RlpFieldRef_is_list := false;
       RlpFieldRef_content_len := 32 |} in
  let cursor := rlp_cursor_advance slice
    (StatelessInputSliceFields_len (RlpFieldRef_source field)) in
  StatelessInputSliceFields_bytes cursor =
    Z.of_nat (length (Z_to_bv 8 160 :: h)) /\
  StatelessInputSliceFields_len cursor = 0.
Proof.
  intros Hlength.
  cbn [rlp_cursor_advance stateless_input_slice_suffix
    stateless_input_sub_slice RlpFieldRef_source
    StatelessInputSliceFields_len StatelessInputSliceFields_bytes List.length].
  rewrite TypeCasts.autocast_refl.
  change (33 = Z.of_nat (S (List.length h)) /\ (0 : Z) = 0).
  change (List.length h = 32%nat) in Hlength.
  rewrite Hlength. split; reflexivity.
Qed.
Print Assumptions sail_parent_first_cursor_end.

Lemma sail_hash_first_byte value :
  nth_error (projT1 (word_to_hash (Build_word value))) O =
    Some (Z_to_bv 8 value).
Proof.
  unfold word_to_hash. cbn [word_value].
  repeat rewrite sail_get_slice_int by lia.
  cbn [B256 vec_update_dec vector_init update_list_dec update_list_inc
    list_update length_list].
  rewrite Z.shiftr_0_r.
  reflexivity.
Qed.
Print Assumptions sail_hash_first_byte.

Lemma sail_fold_nonpalindromic :
  fold_left (fun accumulator (item : byte) =>
    Z.add (Z.mul accumulator 256) (@uint 8 item))
    (List.app (List.repeat (Z_to_bv 8 0) 31%nat) [Z_to_bv 8 1]) 0 = 1.
Proof.
  cbn [List.repeat List.app List.fold_left].
  rewrite !sail_uint_unsigned, !Z_to_bv_unsigned.
  reflexivity.
Qed.
Print Assumptions sail_fold_nonpalindromic.
Lemma sail_hash_byte_order_counterexample :
  projT1 (word_to_hash (Build_word 1)) <>
    (List.app (List.repeat (Z_to_bv 8 0) 31%nat) [Z_to_bv 8 1]).
Proof.
  intro Hhash.
  pose proof (f_equal (fun bytes : list byte => nth_error bytes O) Hhash) as Hfirst.
  cbv beta in Hfirst.
  rewrite sail_hash_first_byte in Hfirst.
  cbn [List.repeat List.app nth_error] in Hfirst.
  injection Hfirst as Hbyte.
  change (bv_unsigned (Z_to_bv 8 1) = bv_unsigned (Z_to_bv 8 0)) in Hbyte.
  rewrite !Z_to_bv_unsigned in Hbyte.
  cbn [bv_wrap bv_modulus] in Hbyte.
  discriminate.
Qed.
Print Assumptions sail_hash_byte_order_counterexample.

Print Assumptions sail_fold_uint_bound.
Print Assumptions sail_word_from_bits_small.

Lemma sail_lookup_same_register (r : register) rs (value : type_of_register r) :
  register_lookup r (register_set r value rs) = value.
Proof. autorewrite with zesu_sail. reflexivity. Qed.
Lemma sail_lookup_other_register (r r' : register) rs
    (value : type_of_register r') :
  register_beq r r' = false ->
  register_lookup r (register_set r' value rs) = register_lookup r rs.
Proof. intros Hdifferent. autorewrite with zesu_sail. reflexivity. Qed.
Lemma sail_guard_boolean_true (x y : Z) :
  Z.ltb x y = true -> (if Z.ltb x y then 1 else 0) = 1.
Proof. sail_eval. Qed.
Lemma sail_guard_boolean_false (x y : Z) :
  Z.leb x y = false -> (if Z.leb x y then 1 else 0) = 0.
Proof. sail_eval. Qed.
Print Assumptions sail_lookup_same_register.
Print Assumptions sail_lookup_other_register.
Print Assumptions sail_guard_boolean_true.
Print Assumptions sail_guard_boolean_false.

Print Assumptions sail_byte_lor_shift.

Print Assumptions sail_fold_uint_little_endian.
