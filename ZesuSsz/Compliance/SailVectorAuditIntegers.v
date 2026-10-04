From Coq Require Import List ZArith String.
From stdpp Require Import bitvector.definitions.
Require Import SailStdpp.MachineWord SailStdpp.Values.
Require Import EvmSailRlp.evm_rlp_types.
Require Import ZesuSsz.Compliance.SailRun.

Import ListNotations.
Open Scope Z_scope.

(* These are direct executions of the pinned Sail item and integer actions.
   They do not classify complete transaction decoding or the selected ELF. *)
Definition integerBytes (values : list Z) : list byte :=
  map (Z_to_bv 8) values.

Definition nineByteNonce : list byte :=
  integerBytes [137; 1; 2; 3; 4; 5; 6; 7; 8; 9].
Definition seventeenByteFee : list byte :=
  integerBytes (145 :: List.repeat 17 17).
Definition leadingZero : list byte :=
  integerBytes [130; 0; 5].
Definition thirtyThreeByteInteger : list byte :=
  integerBytes (161 :: List.repeat 1 33).
Definition canonicalZero : list byte := integerBytes [128].
Definition noncanonicalZero : list byte := integerBytes [0].

Inductive IntegerResult : Type :=
| IntegerSuccess (value : Z)
| IntegerReject
| IntegerUnsupported.

Definition classifyU256 (outcome : SailOutcome word) : IntegerResult :=
  match outcome with
  | Success value => IntegerSuccess value.(word_value)
  | Reject _ => IntegerReject
  | UnsupportedOrInternalFailure _ => IntegerUnsupported
  end.

Definition classifyUint64 (outcome : SailOutcome ssz_uint) : IntegerResult :=
  match outcome with
  | Success value => IntegerSuccess value.(ssz_uint_value)
  | Reject _ => IntegerReject
  | UnsupportedOrInternalFailure _ => IntegerUnsupported
  end.

Definition runIntegerU256 (bytes : list byte) : IntegerResult :=
  let len := Z.of_nat (List.length bytes) in
  match runRlpDecodeItem bytes
    (@Build_StatelessInputSliceFields 0 len 0 len) with
  | Success (existT _ (existT _ field)) =>
      classifyU256 (runRlpDecodeU256 bytes field)
  | Reject _ => IntegerReject
  | UnsupportedOrInternalFailure _ => IntegerUnsupported
  end.

Definition runIntegerUint64 (bytes : list byte) : IntegerResult :=
  let len := Z.of_nat (List.length bytes) in
  match runRlpDecodeItem bytes
    (@Build_StatelessInputSliceFields 0 len 0 len) with
  | Success (existT _ (existT _ field)) =>
      classifyUint64 (runRlpDecodeUint64 bytes field)
  | Reject _ => IntegerReject
  | UnsupportedOrInternalFailure _ => IntegerUnsupported
  end.

Definition integerVectorResults : list (string * IntegerResult * IntegerResult) :=
  [("nonce >8"%string, runIntegerU256 nineByteNonce,
      runIntegerUint64 nineByteNonce);
   ("fee >16"%string, runIntegerU256 seventeenByteFee,
      runIntegerUint64 seventeenByteFee);
   ("leading zero"%string, runIntegerU256 leadingZero,
      runIntegerUint64 leadingZero);
   (">32 bytes"%string, runIntegerU256 thirtyThreeByteInteger,
      runIntegerUint64 thirtyThreeByteInteger);
   ("canonical zero"%string, runIntegerU256 canonicalZero,
      runIntegerUint64 canonicalZero);
   ("noncanonical zero"%string, runIntegerU256 noncanonicalZero,
      runIntegerUint64 noncanonicalZero)].

Definition expectedIntegerVectorResults :
    list (string * IntegerResult * IntegerResult) :=
  [("nonce >8"%string, IntegerSuccess 18591708106338011145,
      IntegerReject);
   ("fee >16"%string, IntegerSuccess 5807485728784016443108259966835510808849,
      IntegerReject);
   ("leading zero"%string, IntegerReject, IntegerReject);
   (">32 bytes"%string, IntegerReject, IntegerReject);
   ("canonical zero"%string, IntegerSuccess 0, IntegerSuccess 0);
   ("noncanonical zero"%string, IntegerReject, IntegerReject)].

Example integerVectorResultsPinned :
  integerVectorResults = expectedIntegerVectorResults.
Proof. vm_compute. reflexivity. Qed.
