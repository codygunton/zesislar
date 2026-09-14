Require Import ZesuSsz.Automation.All.
Require Import isla.riscv64.riscv64.
From Coq Require Import Lists.List ZArith.ZArith.

Lemma exact_transactions_row_cursor (base cursor : bv 64)
    (address : Z) (bytes : list (bv 8)) (total index : nat) :
  bv_unsigned base = address ->
  bv_unsigned cursor = Z.of_nat index ->
  length bytes = (288 * total)%nat ->
  (index < total)%nat ->
  (0x20000000 <= address)%Z ->
  (address + Z.of_nat (length bytes) < 0x40000000)%Z ->
  bv_unsigned (base + cursor * BV 64 288)%bv =
    (address + Z.of_nat (288 * index)%nat)%Z.
Proof.
  intros Hbase Hcursor Hlength Hindex Hmin Hmax.
  have Hoffset : (0 <= 288 * Z.of_nat index < Z.of_nat (length bytes))%Z.
  { rewrite Hlength Nat2Z.inj_mul. cbn. lia. }
  rewrite Nat2Z.inj_mul. cbn. bv_solve.
Qed.
Print Assumptions exact_transactions_row_cursor.

