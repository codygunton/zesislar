From Coq Require Import List String ZArith.
From stdpp Require Import bitvector.definitions.
Require Import EvmSailRlp.evm_rlp_types ZesuSsz.Compliance.SailRun.
Import ListNotations.
Open Scope Z_scope.

(* Source vectors: vectors_test.zig SHA-256 01f13d919075828c9c427ee9be55481760ffb2d1e9ab552e59f4f83f5399c831,
   v13_test.zig SHA-256 611a7268ee26d7214efa54c8ebc9089f1ddba01ea390afb5f8c6dcc3a41219bb.
   These executions concern the pinned Sail RLP item action, not the selected ELF. *)
Definition auditBytes (values : list Z) : list byte := map (Z_to_bv 8) values.
Definition shortList (payload : list Z) : list Z :=
  (192 + Z.of_nat (List.length payload)) :: payload.

Definition legacyFields : list Z :=
  [1; 1; 130; 82; 8; 128; 128; 128; 27; 1; 1].
Definition v1 : list byte := auditBytes (shortList legacyFields).
Definition v2 : list byte := auditBytes (shortList legacyFields ++ [0]).
Definition v3 : list byte := auditBytes (shortList (legacyFields ++ [5])).

Definition typed2Fields : list Z :=
  [1; 1; 1; 1; 130; 82; 8; 128; 128; 128; 192; 1; 1; 1].
Definition v4Suffix : list byte := auditBytes (shortList typed2Fields ++ [255]).
Definition v5 : list byte :=
  auditBytes (shortList
    ([137; 1; 2; 3; 4; 5; 6; 7; 8; 9] ++
     [1; 130; 82; 8; 128; 128; 128; 27; 1; 1])).
Definition v6 : list byte :=
  auditBytes (shortList
    ([168] ++ repeat 170 40 ++
     [1; 130; 82; 8; 128; 128; 128; 27; 1; 1])).
Definition v7 : list byte :=
  auditBytes (shortList
    ([1; 145] ++ repeat 17 17 ++
     [130; 82; 8; 128; 128; 128; 27; 1; 1])).
Definition v8 : list byte :=
  auditBytes (shortList
    [130; 0; 5; 1; 130; 82; 8; 128; 128; 128; 27; 1; 1]).

Definition v9a : list byte := auditBytes [5; 192].
Definition v9b : list byte := auditBytes [0; 192].
Definition v9c : list byte := auditBytes [127; 192].
Definition v9d : list byte := auditBytes [133; 192].
Definition v10Suffix : list byte :=
  auditBytes (shortList
    ([1; 1; 1; 1; 130; 82; 8; 128; 128; 128; 192; 137] ++
     repeat 0 8 ++ [1; 1; 1])).

Definition v11Hashes : list Z :=
  List.concat (repeat (160 :: repeat 2 32) 10).
Definition v11Fields : list Z :=
  [1; 1; 1; 1; 130; 82; 8; 148] ++ repeat 17 20 ++
  [128; 128; 192; 1; 249; 1; 74] ++ v11Hashes ++ [1; 1; 1].
Definition v11Suffix : list byte :=
  auditBytes ([249; 1; 112] ++ v11Fields).
Definition v12 : list byte :=
  auditBytes (shortList
    [1; 1; 130; 82; 8; 133; 1; 2; 3; 4; 5; 128; 128; 27; 1; 1]).
Definition v13 : list byte :=
  auditBytes (shortList
    ([1; 1; 130; 82; 8; 128; 128; 128; 137] ++
     repeat 255 9 ++ [1; 1])).

Definition v5Nonce : list byte :=
  auditBytes [137; 1; 2; 3; 4; 5; 6; 7; 8; 9].
Definition v6Nonce : list byte := auditBytes ([168] ++ repeat 170 40).
Definition v7GasPrice : list byte := auditBytes ([145] ++ repeat 17 17).
Definition v8Nonce : list byte := auditBytes [130; 0; 5].
Definition v10TypedV : list byte :=
  auditBytes ([137] ++ repeat 0 8 ++ [1]).
Definition v11HashList : list byte :=
  auditBytes ([249; 1; 74] ++ v11Hashes).
Definition v12To : list byte := auditBytes [133; 1; 2; 3; 4; 5].
Definition v13LegacyV : list byte :=
  auditBytes ([137] ++ repeat 255 9).

(* Tags: 0 Success, 1 Reject(RlpDecode), 2 UnsupportedOrInternalFailure. *)
Definition sailItemTag (bytes : list byte) : nat :=
  let n := Z.of_nat (List.length bytes) in
  match runRlpDecodeItem bytes (@Build_StatelessInputSliceFields 0 n 0 n) with
  | Success _ => 0%nat
  | Reject _ => 1%nat
  | UnsupportedOrInternalFailure _ => 2%nat
  end.

Definition sailVectorResults : list (string * nat) :=
  [("V1"%string, sailItemTag v1);
   ("V2"%string, sailItemTag v2);
   ("V3"%string, sailItemTag v3);
   ("V4 RLP suffix"%string, sailItemTag v4Suffix);
   ("V5"%string, sailItemTag v5);
   ("V6"%string, sailItemTag v6);
   ("V7"%string, sailItemTag v7);
   ("V8"%string, sailItemTag v8);
   ("V9a"%string, sailItemTag v9a);
   ("V9b"%string, sailItemTag v9b);
   ("V9c"%string, sailItemTag v9c);
   ("V9d"%string, sailItemTag v9d);
   ("V10 RLP suffix"%string, sailItemTag v10Suffix);
   ("V11 RLP suffix"%string, sailItemTag v11Suffix);
   ("V12"%string, sailItemTag v12);
   ("V13"%string, sailItemTag v13);
   ("V5 nonce RLP"%string, sailItemTag v5Nonce);
   ("V6 nonce RLP"%string, sailItemTag v6Nonce);
   ("V7 gas price RLP"%string, sailItemTag v7GasPrice);
   ("V8 nonce RLP"%string, sailItemTag v8Nonce);
   ("V10 typed v RLP"%string, sailItemTag v10TypedV);
   ("V11 hash list RLP"%string, sailItemTag v11HashList);
   ("V12 to RLP"%string, sailItemTag v12To);
   ("V13 legacy v RLP"%string, sailItemTag v13LegacyV)].

Eval vm_compute in sailVectorResults.
