From Coq Require Import Bool Lia List ZArith.
Require Import EvmSailRlp.evm_rlp_types.
Require Import EvmSailRlp.evm_rlp.
Open Scope Z_scope.

(* Sail initialization resets the input register. Install bytes afterward. *)
Definition initializedInput (bytes : list byte) : M unit :=
  SailStdpp.Prompt_monad.bind0 (evm_rlp.sail_model_init tt)
    (write_reg shim_input_bytes bytes).

Lemma inputInstallPreservesProfile (bytes : list byte) (rs : regstate) :
  register_lookup k_execution_profile
    (register_set shim_input_bytes bytes rs) =
  register_lookup k_execution_profile rs.
Proof. destruct rs; reflexivity. Qed.

Lemma shimInputLengthExact (bytes : list byte) :
  evm_rlp.shim_input_length bytes = Z.of_nat (List.length bytes).
Proof. induction bytes; simpl; lia. Qed.

(* The installed byte list backs the complete slice. The generated input
   functions check this condition before they read the list. *)
Definition backedInputSlice (bytes : list byte) (base len : Z) : Prop :=
  0 <= base /\ 0 <= len /\ base + len <= evm_rlp.shim_input_length bytes.

Definition validInputSlice (bytes : list byte) (base len : Z) : bool :=
  (0 <=? base) && (0 <=? len) &&
  (base + len <=? stateless_input_region_bound) &&
  (base + len <=? Z.of_nat (List.length bytes)).

Lemma validInputSliceBacked bytes base len :
  validInputSlice bytes base len = true -> backedInputSlice bytes base len.
Proof.
  unfold validInputSlice, backedInputSlice.
  intros H.
  repeat match goal with
  | H : andb _ _ = true |- _ => apply andb_true_iff in H; destruct H
  end.
  repeat match goal with
  | H : Z.leb _ _ = true |- _ => apply Z.leb_le in H
  end.
  rewrite shimInputLengthExact. lia.
Qed.

(* rlp_ref_hdr length bytes, rlp_decode_list children, rlp_decode_item
   field_source, rlp_item_content, and parent-header field slices all use
   stateless_input_sub_slice. Sail requires 0 <= off, 0 <= size, and
   off + size <= source_len at each call. *)
Lemma subSliceBacked bytes base len off size :
  backedInputSlice bytes base len -> 0 <= off -> 0 <= size ->
  off + size <= len -> backedInputSlice bytes (base + off) size.
Proof. unfold backedInputSlice; lia. Qed.

(* rlp_cursor_advance and stateless_input_slice_suffix use off <= len. *)
Lemma suffixBacked bytes base len off :
  backedInputSlice bytes base len -> 0 <= off -> off <= len ->
  backedInputSlice bytes (base + off) (len - off).
Proof. unfold backedInputSlice; lia. Qed.

Lemma validWordByteCount n :
  ((0 <=? n) && (n <=? 32)) = true -> 0 <= n <= 32.
Proof.
  rewrite andb_true_iff. intros [Hlow Hhigh].
  apply Z.leb_le in Hlow. apply Z.leb_le in Hhigh. lia.
Qed.

(* region_access.sail:157-162 calls byte_at only when off < s.len.
   This covers rlp_ref_hdr, rlp_uint64_width, and all item-byte reads. *)
Lemma sliceByteAccessBound bytes base len off :
  backedInputSlice bytes base len -> 0 <= off -> off < len ->
  0 <= base + off < Z.of_nat (List.length bytes).
Proof. unfold backedInputSlice; rewrite shimInputLengthExact; lia. Qed.

(* region_access.sail:412-417 calls load_n_word only when off < s.len.
   This covers rlp_decode_word and parent-header field loads. *)
Lemma sliceWordStartBound bytes base len off :
  backedInputSlice bytes base len -> 0 <= off -> off < len ->
  0 <= base + off < Z.of_nat (List.length bytes).
Proof. apply sliceByteAccessBound. Qed.

(* input.sail:34 reads a byte only while off + i < s.len. Later bytes are zero. *)
Lemma loadWordByteBound bytes base len off i :
  backedInputSlice bytes base len -> 0 <= off -> 0 <= i ->
  off + i < len ->
  0 <= base + off + i < Z.of_nat (List.length bytes).
Proof. unfold backedInputSlice; rewrite shimInputLengthExact; lia. Qed.
