From Coq Require Import List ZArith.
Require Import SailStdpp.MachineWord SailStdpp.Prompt_monad.
Require Import EvmSailRlp.evm_rlp_types EvmSailRlp.evm_rlp.
Require Import ZesuSsz.Compliance.RlpInputBounds ZesuSsz.Compliance.SailRun.

Open Scope Z_scope.

(* Each relation uses one public wrapper with a fixed generated action,
   initialized input register, initial state, and concrete evaluator. *)
Definition ReferenceRlpItem {base len : Z} (bytes : list byte)
    (cursor : RlpCursor base len)
    (outcome : SailOutcome
      ({full_len & {content_len & RlpFieldRef base full_len content_len}}%type))
    : Prop :=
  validInputSlice bytes base len = true /\
  runRlpDecodeItem bytes cursor = outcome.

Definition ReferenceRlpHeader {base len : Z} (bytes : list byte)
    (cursor : StatelessInputSliceFields base len)
    (outcome : SailOutcome (bool * source_pointer * Z)) : Prop :=
  validInputSlice bytes base len = true /\
  runRlpRefHdr bytes cursor = outcome.

Definition ReferenceRlpNode {base len : Z} (bytes : list byte)
    (node : StatelessInputSliceFields base len)
    (outcome : SailOutcome
      ({source_len & {source_off & RlpCursor source_off source_len}}%type))
    : Prop :=
  validInputSlice bytes base len = true /\
  runRlpNodeCursor bytes node = outcome.

Definition ReferenceParentHeaderFields {base len : Z} (bytes : list byte)
    (cursor : StatelessInputSliceFields base len)
    (fieldIndex : parent_header_field_cursor) (fields : ParentHeaderFields)
    (outcome : SailOutcome ParentHeaderFields) : Prop :=
  validInputSlice bytes base len = true /\
  0 <= parent_header_field_cursor_value fieldIndex <= 19 /\
  runParentHeaderFields bytes cursor fieldIndex fields = outcome.
