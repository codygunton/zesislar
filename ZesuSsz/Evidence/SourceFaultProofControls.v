Require Import ZesuSsz.Automation.All.
Require Import isla.riscv64.riscv64.
From Coq Require Import Lists.List ZArith.ZArith NArith.NArith Bool.Bool.
Require Import stdpp.bitvector.definitions.
Require Import ZesuSsz.Contracts.RlpDecodeItemContract.
Require Import ZesuSsz.Contracts.RlpDecodeItem.
Require Import ZesuSsz.Contracts.DecodeItemCompositional.
Open Scope Z_scope.

Require Import ZesuSsz.Automation.SourceFaultProof.

Lemma composition403_fault0 (args : DecodeItemArgs) :
 decodeItemArgsWellFormed args ->
 ((negb (bool_decide ((bv_signed (bv_add (bv_zero_extend 128%N (bv_add (bv_add ((Z_to_bv 64%N (decodeItemStackPointer args))) (BV 64%N 18446744073709551600%Z)) (BV 64%N 8%Z))) (BV 128%N 8%Z)) <= bv_signed (BV 128%N 3221225472%Z))%Z))) = true) -> False.
Proof.
intros Hdomain Hleaf.
assert (source_fault_enabled : ZesuStepSourceFaultProof) by constructor.
zesu_source_fault_proof ltac:(
  unfold decodeItemArgsWellFormed, decodeItemEntryLayout in Hdomain;
  cbn [decodeItemStackBytes word64Modulus machineRamEnd defaultMap] in Hdomain) Hleaf.

Qed.
Lemma composition403_fault1 (args : DecodeItemArgs) :
 decodeItemArgsWellFormed args ->
 ((negb (bool_decide ((bv_signed (bv_zero_extend 128%N (bv_add (bv_add ((Z_to_bv 64%N (decodeItemStackPointer args))) (BV 64%N 18446744073709551600%Z)) (BV 64%N 8%Z))) >= bv_signed (BV 128%N 2684354560%Z))%Z))) = true) -> False.
Proof.
intros Hdomain Hleaf.
assert (source_fault_enabled : ZesuStepSourceFaultProof) by constructor.
zesu_source_fault_proof ltac:(
  unfold decodeItemArgsWellFormed, decodeItemEntryLayout in Hdomain;
  cbn [decodeItemStackBytes word64Modulus machineRamEnd defaultMap] in Hdomain) Hleaf.

Qed.
Lemma composition403_fault2 (args : DecodeItemArgs) :
 decodeItemArgsWellFormed args ->
 ((negb (bool_decide ((bv_signed (bv_add (bv_zero_extend 128%N (bv_add ((Z_to_bv 64%N (decodeItemStackPointer args))) (BV 64%N 18446744073709551600%Z))) (BV 128%N 8%Z)) <= bv_signed (BV 128%N 3221225472%Z))%Z))) = true) -> False.
Proof.
intros Hdomain Hleaf.
assert (source_fault_enabled : ZesuStepSourceFaultProof) by constructor.
zesu_source_fault_proof ltac:(
  unfold decodeItemArgsWellFormed, decodeItemEntryLayout in Hdomain;
  cbn [decodeItemStackBytes word64Modulus machineRamEnd defaultMap] in Hdomain) Hleaf.

Qed.
Lemma composition403_fault3 (args : DecodeItemArgs) :
 decodeItemArgsWellFormed args ->
 ((negb (bool_decide ((bv_signed (bv_zero_extend 128%N (bv_add ((Z_to_bv 64%N (decodeItemStackPointer args))) (BV 64%N 18446744073709551600%Z))) >= bv_signed (BV 128%N 2684354560%Z))%Z))) = true) -> False.
Proof.
intros Hdomain Hleaf.
assert (source_fault_enabled : ZesuStepSourceFaultProof) by constructor.
zesu_source_fault_proof ltac:(
  unfold decodeItemArgsWellFormed, decodeItemEntryLayout in Hdomain;
  cbn [decodeItemStackBytes word64Modulus machineRamEnd defaultMap] in Hdomain) Hleaf.

Qed.
Lemma source_fault_generic_upper (base limit : Z)
    (Hbase : 0 <= base < 2^64) (Hlimit : base <= limit)
    (Hleaf : negb (bool_decide
      (bv_signed (bv_zero_extend 128 (Z_to_bv 64 base)) <= limit)) = true) : False.
Proof.
Fail zesu_source_fault_proof ltac:(idtac) Hleaf.
assert (source_fault_enabled : ZesuStepSourceFaultProof) by constructor.
zesu_source_fault_proof ltac:(idtac) Hleaf.

Qed.
Lemma source_fault_generic_lower (base limit : Z)
    (Hbase : 0 <= base < 2^64) (Hlimit : limit <= base)
    (Hleaf : negb (bool_decide
      (bv_signed (bv_zero_extend 128 (Z_to_bv 64 base)) >= limit)) = true) : False.
Proof.
assert (source_fault_enabled : ZesuStepSourceFaultProof) by constructor.
zesu_source_fault_proof ltac:(idtac) Hleaf.

Qed.
Lemma source_fault_missing_bound (base limit : Z)
    (Hbase : 0 <= base < 2^64)
    (Hleaf : negb (bool_decide
      (bv_signed (bv_zero_extend 128 (Z_to_bv 64 base)) <= limit)) = true) : True.
Proof.
assert (source_fault_enabled : ZesuStepSourceFaultProof) by constructor.
Fail assert (Hfalse : False) by (zesu_source_fault_proof ltac:(idtac) Hleaf).
exact I.

Qed.
Lemma source_fault_missing_nonwrap (base limit : Z)
    (Hbase : base < 2^64) (Hlimit : base <= limit)
    (Hleaf : negb (bool_decide
      (bv_signed (bv_zero_extend 128 (Z_to_bv 64 base)) <= limit)) = true) : True.
Proof.
assert (source_fault_enabled : ZesuStepSourceFaultProof) by constructor.
Fail assert (Hfalse : False) by (zesu_source_fault_proof ltac:(idtac) Hleaf).
exact I.

Qed.
Lemma source_fault_unsupported_root (word : bv 64) (limit : Z)
    (Hlimit : bv_unsigned word <= limit)
    (Hleaf : negb (bool_decide
      (bv_signed (bv_zero_extend 128 word) <= limit)) = true) : True.
Proof.
assert (source_fault_enabled : ZesuStepSourceFaultProof) by constructor.
Fail assert (Hfalse : False) by (zesu_source_fault_proof ltac:(idtac) Hleaf).
exact I.

Qed.
Lemma source_fault_symbolic_offset (base limit : Z) (offset : bv 64)
    (Hbase : 0 <= base < 2^64)
    (Hleaf : negb (bool_decide
      (bv_signed (bv_zero_extend 128 (Z_to_bv 64 base + offset)) <= limit)) = true) : True.
Proof.
assert (source_fault_enabled : ZesuStepSourceFaultProof) by constructor.
Fail zesu_source_fault_closed_offsets (Z_to_bv 64 base + offset).
Fail assert (Hfalse : False) by (zesu_source_fault_proof ltac:(idtac) Hleaf).
exact I.

Qed.
Lemma source_fault_unsupported_width (base limit : Z)
    (Hbase : 0 <= base < 2^32) (Hlimit : base <= limit)
    (Hleaf : negb (bool_decide
      (bv_signed (bv_zero_extend 128 (Z_to_bv 32 base)) <= limit)) = true) : True.
Proof.
assert (source_fault_enabled : ZesuStepSourceFaultProof) by constructor.
Fail assert (Hfalse : False) by (zesu_source_fault_proof ltac:(idtac) Hleaf).
exact I.

Qed.

Lemma source_offset_closed_positive : bv_unsigned (BV 128 1) < 2 ^ 64.
Proof. zesu_source_fault_offset_bound. Qed.

Lemma source_offset_closed_false_refuses : True.
Proof.
  Fail assert ((2 : Z) < 1) by zesu_source_fault_offset_bound.
  exact I.
Qed.

Lemma source_offset_symbolic_vm_refuses (offset : bv 128) : True.
Proof.
  Fail VmClosed.zesu_vm_closed constr:(bv_unsigned offset).
  exact I.
Qed.

Lemma source_offset_symbolic_fallback (offset : bv 128)
    (Hsmall : bv_unsigned offset < 2 ^ 64) :
    bv_unsigned offset < 2 ^ 64.
Proof. zesu_source_fault_offset_bound. Qed.
