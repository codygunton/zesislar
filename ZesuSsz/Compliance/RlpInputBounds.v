From Coq Require Import Lia List ZArith.
Require Import EvmSailRlp.evm_rlp_types.
Require Import EvmSailRlp.evm_rlp.

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

(* region_access.sail:157-162 calls byte_at only when off < s.len. *)
Lemma sliceByteAccessBound bytes base len off :
  backedInputSlice bytes base len -> 0 <= off -> off < len ->
  0 <= base + off < Z.of_nat (List.length bytes).
Proof. unfold backedInputSlice; rewrite shimInputLengthExact; lia. Qed.

(* region_access.sail:412-417 calls load_n_word only when off < s.len. *)
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
