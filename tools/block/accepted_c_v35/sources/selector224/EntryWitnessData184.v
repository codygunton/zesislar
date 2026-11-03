From Coq Require Import Lists.List Strings.String ZArith.ZArith NArith.NArith.
Require Import stdpp.bitvector.definitions.
Require Import lithium.lvar.
Require Import ZesuSsz.Contracts.RlpDecodeItemContract.
Open Scope Z_scope.
Open Scope string_scope.

Definition entry6ac4_prefix184 (args : DecodeItemArgs) : bv 8%N :=
  List.nth 0%nat (decodeItemInputBytes args) (BV 8%N 0%Z).
Definition entry6ac4_rest184 (args : DecodeItemArgs) : list (bv 8%N) :=
  skipn 1%nat (decodeItemInputBytes args).
Definition entry6ac4_count184 (args : DecodeItemArgs) : lvar "zesuLoopCount" Z :=
  bv_unsigned (entry6ac4_prefix184 args) - 247.
Definition entry6ac4_index184 : lvar "zesuLoopIndex" Z := 0%Z.
Definition entry6ac4_payloadStart184 (args : DecodeItemArgs) : Z :=
  decodeItemInputPointer args + 1.
Definition entry6ac4_lengthBytes184 (args : DecodeItemArgs) : list (bv 8%N) :=
  firstn (Z.to_nat (entry6ac4_count184 args)) (entry6ac4_rest184 args).
Definition entry6ac4_loaded184 (a6 : bv 64%N) : bv 64%N := a6.

Definition Entry6ac4WitnessType184 : Type :=
  (bv 8%N * (list (bv 8%N) * (lvar "zesuLoopCount" Z *
   (lvar "zesuLoopIndex" Z * (Z * (list (bv 8%N) * (bv 64%N * unit)))))))%type.

Definition entry6ac4_witness_data184 (args : DecodeItemArgs) (a6 : bv 64%N)
    : Entry6ac4WitnessType184 :=
  (entry6ac4_prefix184 args,
   (entry6ac4_rest184 args,
    (entry6ac4_count184 args,
     (entry6ac4_index184,
      (entry6ac4_payloadStart184 args,
       (entry6ac4_lengthBytes184 args, (entry6ac4_loaded184 a6, tt))))))).
