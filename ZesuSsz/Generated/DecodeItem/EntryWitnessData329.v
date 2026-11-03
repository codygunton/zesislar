From Coq Require Import Lists.List Strings.String ZArith.ZArith NArith.NArith.
Require Import stdpp.bitvector.definitions.
Require Import lithium.lvar.
Require Import ZesuSsz.Contracts.RlpDecodeItemContract.
Open Scope Z_scope.
Open Scope string_scope.
Open Scope list_scope.

Definition Entry6a24FullWitnessType329 : Type :=
 (bv 8%N * (list (bv 8%N) * (lvar "zesuLoopCount" Z * (lvar "zesuLoopIndex" Z * (Z * (list (bv 8%N) * (list (bv 8%N) * (bv 64%N * (bv 64%N * (bv 64%N * (bv 64%N * (bv 64%N * (bv 64%N * (bv 64%N * (bv 64%N * (bv 64%N * (bv 64%N * (bv 64%N * unit)%type)%type)%type)%type)%type)%type)%type)%type)%type)%type)%type)%type)%type)%type)%type)%type)%type)%type.

Definition entry6a24_full_witness_data329 (args : DecodeItemArgs) (source_x10 source_x11 source_x12 source_x13 source_x14 source_x15 source_x16 source_x2 source_x1 source_x8 : bv 64%N)
 : Entry6a24FullWitnessType329 :=
 ((List.nth 0%nat (decodeItemInputBytes args) (BV 8%N 0%Z)), ((skipn 1%nat (decodeItemInputBytes args)), (((bv_unsigned (List.nth 0%nat (decodeItemInputBytes args) (BV 8%N 0%Z)) - 183)%Z), ((0%Z), (((decodeItemInputPointer args + 1)%Z), ((firstn (Z.to_nat ((bv_unsigned (List.nth 0%nat (decodeItemInputBytes args) (BV 8%N 0%Z)) - 183)%Z)) (skipn 1%nat (decodeItemInputBytes args))), ((((bv_to_little_endian (Z.of_nat 8%nat) 8%N (bv_unsigned (decodeItemSavedFramePointer args))) ++ (bv_to_little_endian (Z.of_nat 8%nat) 8%N (bv_unsigned ((Z_to_bv 64%N (decodeItemReturnAddress args))))))), ((source_x16), ((source_x10), ((bv_add source_x11 (bv_add source_x14 (BV 64%N 1%Z))), ((source_x12), ((BV 64%N 0%Z), ((bv_add source_x14 (BV 64%N 1%Z)), ((bv_add source_x11 (BV 64%N 1%Z)), ((source_x16), ((source_x2), ((source_x1), ((source_x8), tt)))))))))))))))))).

Definition Entry6a24RemainingWitnessType329 : Type :=
 (lvar "zesuLoopCount" Z * (lvar "zesuLoopIndex" Z * (Z * (list (bv 8%N) * (bv 64%N * unit)%type)%type)%type)%type)%type.

Definition entry6a24_remaining_witness_data329 (args : DecodeItemArgs) (source_x16 : bv 64%N)
 : Entry6a24RemainingWitnessType329 :=
 (((bv_unsigned (List.nth 0%nat (decodeItemInputBytes args) (BV 8%N 0%Z)) - 183)%Z), ((0%Z), (((decodeItemInputPointer args + 1)%Z), ((firstn (Z.to_nat ((bv_unsigned (List.nth 0%nat (decodeItemInputBytes args) (BV 8%N 0%Z)) - 183)%Z)) (skipn 1%nat (decodeItemInputBytes args))), ((source_x16), tt))))).
