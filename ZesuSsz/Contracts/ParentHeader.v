From Coq Require Import List String ZArith Lia.
From stdpp Require Import bitvector.definitions.
Require Import SailStdpp.MachineWord SailStdpp.Values.
Require Import EvmSailRlp.evm_rlp_types.
Require Import ZesuSsz.Contracts.RlpDecodeItem.

Import ListNotations.
Open Scope Z_scope.

(* Read-only ELF: .worktrees/p0c-stock-target/build/stock-zisk/zesu-zisk.elf.
   SHA256 e44c18d54ae3d77832df92aceb6eb7119de8eb2e8f1f1b4e585a6e33ea04ff95.
   The selected symbol table gives these complete function ranges. *)
Definition parentHeaderElfSha256 : string :=
  "e44c18d54ae3d77832df92aceb6eb7119de8eb2e8f1f1b4e585a6e33ea04ff95"%string.
Definition decodeParentHeaderEntry : Z := 0x800d5cb8.
Definition decodeParentHeaderEnd : Z := 0x800d6274.
Definition nextUint64Entry : Z := 0x800d6274.
Definition nextUint64End : Z := 0x800d6348.

(* The ELF writes the result through s1. Stores at 0x800d607c..0x800d6098
   and 0x800d61e4..0x800d6208 identify these offsets. Optional tags occupy
   their first byte; their seven padding bytes have no value condition. *)
Definition parentHeaderResultBytes : nat := 72%nat.
Definition gasLimitOffset : nat := 0%nat.
Definition gasUsedOffset : nat := 8%nat.
Definition timestampOffset : nat := 16%nat.
Definition baseFeeValueOffset : nat := 24%nat.
Definition baseFeeTagOffset : nat := 32%nat.
Definition blobGasValueOffset : nat := 40%nat.
Definition blobGasTagOffset : nat := 48%nat.
Definition excessBlobGasValueOffset : nat := 56%nat.
Definition excessBlobGasTagOffset : nat := 64%nat.

Definition optionalWordAt (bytes : list byte) (valueOffset tagOffset : nat)
    (value : option Z) : Prop :=
  byteAt bytes tagOffset (if value then 1 else 0) /\
  match value with
  | Some n => word64At bytes valueOffset n
  | None => True
  end.

Record ParentHeaderValue := {
  parentGasLimit : Z;
  parentGasUsed : Z;
  parentTimestamp : Z;
  parentBaseFee : option Z;
  parentBlobGas : option Z;
  parentExcessBlobGas : option Z;
}.

Definition parentHeaderResult72 (bytes : list byte)
    (header : ParentHeaderValue) : Prop :=
  List.length bytes = parentHeaderResultBytes /\
  word64At bytes gasLimitOffset header.(parentGasLimit) /\
  word64At bytes gasUsedOffset header.(parentGasUsed) /\
  word64At bytes timestampOffset header.(parentTimestamp) /\
  optionalWordAt bytes baseFeeValueOffset baseFeeTagOffset
    header.(parentBaseFee) /\
  optionalWordAt bytes blobGasValueOffset blobGasTagOffset
    header.(parentBlobGas) /\
  optionalWordAt bytes excessBlobGasValueOffset excessBlobGasTagOffset
    header.(parentExcessBlobGas).

(* The selected ELF checks payload length <= 8 at 0x800d62d0..0x800d62d4,
   folds each byte at 0x800d6318..0x800d6324, and returns a 16-byte
   result at 0x800d633c..0x800d6340. A rejected item writes error tag 3
   at 0x800d62d8..0x800d62e0. *)
Definition nextUint64ByteFold (payload : list byte) (value : Z) : Prop :=
  (List.length payload <= 8)%nat /\
  value = List.fold_left
    (fun acc b => 256 * acc + bv_unsigned b) payload 0.

Definition nextUint64Success16 (result : list byte)
    (payload : list byte) : Prop :=
  List.length result = 16%nat /\
  nextUint64ByteFold payload (littleEndian (firstn 8 result)) /\
  byteAt result 8 0 /\ byteAt result 9 0.

Definition nextUint64Error16 (result : list byte) : Prop :=
  List.length result = 16%nat /\
  word64At result 0 0 /\ word64At result 8 3.

Lemma nextUint64ByteFold_empty : nextUint64ByteFold [] 0.
Proof. split; [simpl; lia | reflexivity]. Qed.

Lemma nextUint64ByteFold_value payload value :
  nextUint64ByteFold payload value -> value = bigEndian payload.
Proof. intros [_ Hvalue]. exact Hvalue. Qed.

(* decodeParentHeader invokes decodeItem once for its outer list, nine times
   for skipped fields 0..8, three times for skipped fields 12..14, and once
   for skipped field 16 when present. Each nextUint64 calls decodeItem for
   fields 9, 10, 11, 15, 17, and 18 when present. There are at most 20
   nested calls. A nested length wrap uses the C1-B known-bug relation.
   This counterexample shows that a fitting outer header does not rule it out. *)
Definition hostileNestedHeader : list byte :=
  mword_of_int 191 :: List.repeat (mword_of_int 255) 8.

Definition fittingOuterHeader : list byte :=
  mword_of_int 201 :: hostileNestedHeader.

Lemma outerHeaderFits : headerFits fittingOuterHeader.
Proof. vm_compute. auto. Qed.

Lemma nestedHeaderDoesNotFit : ~ headerFits hostileNestedHeader.
Proof. vm_compute. intuition discriminate. Qed.
