Require Import ZesuSsz.Automation.All.
Require Import ZesuMachineMap.Machine.
Require Import isla.riscv64.riscv64.
From Coq Require Import ZArith.ZArith Lists.List.

Lemma transactions_index_cursor (base : Z) (bytes : list (bv 8)) (processed : nat) :
  ((mapRamBase defaultMap) <= base)%Z ->
  (base + Z.of_nat (length bytes) < (machineRamEnd defaultMap))%Z ->
  (288 * processed + 288 <= length bytes)%nat -> base `mod` 8 = 0 ->
  let row := (Z_to_bv 64 base + Z_to_bv 64 (Z.of_nat processed) * BV 64 288)%bv in
  bv_unsigned row = (base + Z.of_nat (288 * processed))%Z /\
  bv_unsigned row `mod` 8 = 0.
Proof.
  intros Hbase Hend Hbound HbaseAlign. cbn zeta.
  have Hcursor : bv_unsigned (Z_to_bv 64 base + Z_to_bv 64 (Z.of_nat processed) * BV 64 288)%bv = (base + Z.of_nat (288 * processed))%Z.
  { rewrite Nat2Z.inj_mul. clear -Hbase Hend Hbound. bv_solve. }
  split; first exact Hcursor. rewrite Hcursor Nat2Z.inj_mul.
  apply Z.mod_divide; first lia.
  apply Z.mod_divide in HbaseAlign; last lia.
  destruct HbaseAlign as [k Hk]. exists (k + 36 * Z.of_nat processed). lia.
Qed.
Print Assumptions transactions_index_cursor.
