From Coq Require Import List ZArith.
From stdpp Require Import bitvector.definitions.
Require Import SailStdpp.MachineWord.
Require Import EvmSailRlp.evm_rlp_types.

Import ListNotations.
Open Scope Z_scope.

Definition word64Bytes (value : Z) : list byte :=
  List.map (fun offset => Z_to_bv 8
    (Z.shiftr value (8 * Z.of_nat offset))) (List.seq 0 8).

Example word64Bytes80 :
  word64Bytes 80 = List.map (Z_to_bv 8) [80; 0; 0; 0; 0; 0; 0; 0].
Proof. vm_compute. reflexivity. Qed.
