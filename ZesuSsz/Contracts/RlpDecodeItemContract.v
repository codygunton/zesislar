From Coq Require Import List ZArith.
Require Import EvmSailRlp.evm_rlp_types.
Require Import ZesuSsz.Contracts.Level1.
Require Import ZesuSsz.Contracts.RlpDecodeItem.

(* The ABI assigns a0 to output, a1 to input, and a2 to input length.
   The caller owns the 40-byte result and the 16-byte stack frame. *)
Record DecodeItemArgs : Type := {
  decodeItemOutputPointer : Z;
  decodeItemInputPointer : Z;
  decodeItemInputLength : Z;
  decodeItemInputBytes : list byte;
  decodeItemBeforeStorage : list byte;
  decodeItemStackPointer : Z;
  decodeItemReturnAddress : Z
}.

Definition DecodeItemOutcome : Type := list byte.

Definition decodeItemArgsWellFormed (args : DecodeItemArgs) : Prop :=
  decodeItemInputLength args = Z.of_nat (List.length (decodeItemInputBytes args)) /\
  (List.length (decodeItemBeforeStorage args) = 40)%nat /\
  decodeItemEntryLayout
    (decodeItemInputPointer args) (decodeItemInputLength args)
    (decodeItemOutputPointer args) (decodeItemStackPointer args)
    (decodeItemReturnAddress args).

Definition decodeItemC1ADomain (args : DecodeItemArgs) : Prop :=
  decodeItemArgsWellFormed args /\ headerFits (decodeItemInputBytes args).

Definition decodeItemC1BDomain (args : DecodeItemArgs) : Prop :=
  decodeItemArgsWellFormed args.

Definition decodeItemAllows
    (R : Z -> list byte -> list byte -> list byte -> Prop)
    (args : DecodeItemArgs) (after : DecodeItemOutcome) : Prop :=
  R (decodeItemInputPointer args) (decodeItemInputBytes args)
    (decodeItemBeforeStorage args) after.

Definition decodeItemAllowsC1A : DecodeItemArgs -> DecodeItemOutcome -> Prop :=
  decodeItemAllows C1AResult.

Definition decodeItemAllowsC1B : DecodeItemArgs -> DecodeItemOutcome -> Prop :=
  decodeItemAllows C1BResult.
