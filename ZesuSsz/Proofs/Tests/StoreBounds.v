Require Import ZesuSsz.Automation.All.
Require Import ZesuSsz.Automation.ByteArrayLengths.
Require Import ZesuSsz.Automation.Switches.ArrayBounds.
Require Import ZesuSsz.Automation.Switches.ArrayRegionBounds.
Require Import ZesuSsz.Automation.Switches.TupleWitness.
Require Import ZesuSsz.Compliance.DecodeItemHeaderWitnessFacts.
Require Import ZesuSsz.Contracts.RlpDecodeItemBlockEntries.
Require Import isla.riscv64.riscv64.
From Coq Require Import List ZArith.
Open Scope Z_scope.

Lemma store_updated_width (out : Z) (storage : list byte) (value : byte)
    (Hlength : length storage = 40%nat) :
  (Z.to_nat (out + 8 - out) + N.to_nat 8 <=
    length (<[16%nat := value]>
      (take 8 storage ++ drop 8 storage)))%nat.
Proof. zesu_array_bounds_if_enabled. Qed.

Lemma store_updated_strict (out : Z) (storage : list byte) (value : byte)
    (Hlength : length storage = 40%nat) :
  (Z.to_nat ((out + 16 - out) `div` 1) <
    length (<[8%nat := value]> storage))%nat.
Proof. zesu_array_bounds_if_enabled. Qed.

Lemma store_invalid_width (out : Z) (storage : list byte)
    (Hlength : length storage = 8%nat) : True.
Proof.
  Fail assert (Hbad :
    (Z.to_nat (out + 8 - out) + N.to_nat 8 <= length storage)%nat)
    by zesu_array_bounds_if_enabled.
  exact I.
Qed.

Lemma store_nonbyte_lengths (storage : list (bv 16)) : True.
Proof.
  Fail assert (Hbad : (0 <= length storage)%nat)
    by zesu_byte_array_lengths_if_enabled.
  exact I.
Qed.

Lemma store_nat_opener_guard `{!islaG Sigma} `{!threadG} :
  ⊢ ((∃ index : nat, ⌜index = 3%nat⌝)%I : iProp Sigma).
Proof.
  iStartProof.
  Fail zesu_primitive_tuple_if_enabled.
  iExists 3%nat. done.
Qed.

Lemma store_protected_nat_guard `{!islaG Sigma} `{!threadG} :
  ⊢ ((∃ index : li_prod nat unit, ⌜index.1ₗ = 3%nat⌝)%I : iProp Sigma).
Proof.
  iStartProof.
  Fail zesu_primitive_tuple_if_enabled.
  iExists (3%nat, tt)ₗ. done.
Qed.

Print Assumptions store_updated_width.
Print Assumptions store_updated_strict.
Print Assumptions store_nat_opener_guard.
Print Assumptions store_protected_nat_guard.

Lemma store_restored_sp (SP : Z) :
  (Z_to_bv 64 (SP - RlpDecodeItem.decodeItemStackBytes) + 16)%bv = Z_to_bv 64 SP.
Proof. zesu_finish_contract_arithmetic. Qed.

Lemma store_restored_sp_wrong_offset (SP : Z) : True.
Proof.
  Fail assert (Hbad :
    (Z_to_bv 64 (SP - RlpDecodeItem.decodeItemStackBytes) + 8)%bv = Z_to_bv 64 SP)
    by zesu_finish_contract_arithmetic.
  exact I.
Qed.

Lemma store_frame_end (SP : Z) (locals : DecodeItemReturnLocals)
    (Hsp : (RlpDecodeItem.decodeItemStackBytes <= SP < 2 ^ 64)%Z)
    (Hlength : length (returnFrame locals) = 16%nat) :
  (SP - RlpDecodeItem.decodeItemStackBytes +
    Z.of_nat (length (returnFrame locals)) <= 2 ^ 64)%Z.
Proof. zesu_finish_contract_arithmetic. Qed.

Lemma store_frame_end_wrong_offset (SP : Z) (locals : DecodeItemReturnLocals)
    (Hsp : (RlpDecodeItem.decodeItemStackBytes <= SP < 2 ^ 64)%Z)
    (Hlength : length (returnFrame locals) = 16%nat) : True.
Proof.
  Fail assert (Hbad :
    (SP - RlpDecodeItem.decodeItemStackBytes + 8 +
      Z.of_nat (length (returnFrame locals)) <= 2 ^ 64)%Z)
    by zesu_finish_contract_arithmetic.
  exact I.
Qed.

Print Assumptions store_restored_sp.
Print Assumptions store_restored_sp_wrong_offset.
Print Assumptions store_frame_end.
Print Assumptions store_frame_end_wrong_offset.

Lemma store_updated_total (storage : list byte) (value : bv 64)
    (Hlength : length storage = 40%nat) :
  length (take 24 (<[16%nat := BV 8 0]> storage) ++
    bv_to_little_endian 8 8 (bv_unsigned value) ++
    drop 32 (<[16%nat := BV 8 0]> storage)) = 40%nat.
Proof. zesu_finish_contract_arithmetic. Qed.

Lemma store_updated_wrong_total (storage : list byte) (value : bv 64)
    (Hlength : length storage = 40%nat) : True.
Proof.
  Fail assert (Hbad :
    length (take 24 (<[16%nat := BV 8 0]> storage) ++
      bv_to_little_endian 8 8 (bv_unsigned value) ++
      drop 32 (<[16%nat := BV 8 0]> storage)) = 39%nat)
    by zesu_finish_contract_arithmetic.
  exact I.
Qed.

Print Assumptions store_updated_total.
Print Assumptions store_updated_wrong_total.
