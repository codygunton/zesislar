From Coq Require Import List ZArith.
Require Import SailStdpp.MachineWord.
Require Import EvmSailRlp.evm_rlp_types EvmSailRlp.evm_rlp.
Require Import ZesuSsz.Contracts.ParentHeader.
Require Import ZesuSsz.Compliance.RlpInputBounds ZesuSsz.Compliance.SailRun.

Open Scope Z_scope.

(* This is the generated EMPTY_PARENT_HEADER_FIELDS value from the pinned
   stateless_input.sail:664-675. No decoder or evaluator is supplied by a
   caller. *)
Definition emptyParentFields : ParentHeaderFields :=
  Build_ParentHeaderFields
    (evm_rlp.word_to_hash (Build_word 0))
    (evm_rlp.word_to_hash (Build_word 0))
    (Build_word 0) 0 (Build_excess_blob_gas_typ 0)
    false false false false false.

Definition sailParentHeaderRun {base len : Z} (bytes : list byte)
    (node : StatelessInputSliceFields base len)
    : SailOutcome ParentHeaderFields :=
  match runRlpNodeCursor bytes node with
  | Success (existT _ (existT _ cursor)) =>
      runParentHeaderFields bytes cursor
        (Build_parent_header_field_cursor 0) emptyParentFields
  | Reject error => Reject error
  | UnsupportedOrInternalFailure message =>
      UnsupportedOrInternalFailure message
  end.

Definition ParentHeaderSailRelation {base len : Z} (bytes : list byte)
    (node : StatelessInputSliceFields base len)
    (outcome : SailOutcome ParentHeaderFields) : Prop :=
  validInputSlice bytes base len = true /\
  sailParentHeaderRun bytes node = outcome.

(* Sail records only parent hash, state root, base fee, and blob-gas fields.
   It does not return Zig's gas limit, gas used, or timestamp. Their binary
   values stay in ParentHeaderValue and need another specification boundary. *)
Definition sailOptionalWord (present : bool) (value : Z)
    (machineValue : option Z) : Prop :=
  if present then
    machineValue = Some value /\ 0 <= value < 2 ^ 64
  else machineValue = None.

Definition ParentHeaderSharedFields (sail : ParentHeaderFields)
    (binary : ParentHeaderValue) : Prop :=
  sailOptionalWord sail.(ParentHeaderFields_have_base_fee)
    sail.(ParentHeaderFields_base_fee).(word_value)
    binary.(parentBaseFee) /\
  sailOptionalWord sail.(ParentHeaderFields_have_blob_gas)
    sail.(ParentHeaderFields_blob_gas_used)
    binary.(parentBlobGas) /\
  sailOptionalWord sail.(ParentHeaderFields_have_excess_blob_gas)
    sail.(ParentHeaderFields_excess_blob_gas).(excess_blob_gas_value)
    binary.(parentExcessBlobGas).

Definition ParentHeaderSuccess {base len : Z} (bytes : list byte)
    (node : StatelessInputSliceFields base len)
    (binary : ParentHeaderValue) : Prop :=
  exists sail,
    ParentHeaderSailRelation bytes node (Success sail) /\
    ParentHeaderSharedFields sail binary.

Definition ParentHeaderRejects {base len : Z} (bytes : list byte)
    (node : StatelessInputSliceFields base len) : Prop :=
  ParentHeaderSailRelation bytes node (Reject RlpDecode).
