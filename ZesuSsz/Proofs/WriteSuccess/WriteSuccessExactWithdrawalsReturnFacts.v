Require Import ZesuSsz.Automation.AllLegacy.
Require Import isla.riscv64.riscv64.
From Coq Require Import Lists.List ZArith.ZArith.
From ZesuSsz.Proofs.WriteSuccess Require Import
  WriteSuccessExactWithdrawalsLoopSpec.

Lemma withdrawal_facts_advance sp pointer base rows prefix row next rest source :
  withdrawalLoopFacts sp pointer base rows prefix row (next :: rest) source ->
  withdrawalLoopFacts sp (pointer + BV 64 48)%bv base rows
    (prefix ++ [row]) next rest source.
Proof.
  intros Hfacts.
  pose proof (withdrawal_facts_layout sp pointer base rows prefix row (next :: rest) source Hfacts)
    as (Hprefix & Hrow & Hslice & Hlength).
  destruct Hfacts as (Hrows & Hall & Hbytes & Hposition & Hcount & Halign & Hlow & Hhigh & Hbase & Hend).
  apply (f_equal Z.of_nat) in Hlength.
  rewrite Nat2Z.inj_mul Nat2Z.inj_add !Nat2Z.inj_succ in Hlength. cbn in Hlength.
  have Hadvance : bv_unsigned (pointer + BV 64 48)%bv =
    (base + 48 * Z.of_nat (length (prefix ++ [row])))%Z.
  { rewrite app_length /= Nat2Z.inj_add /=. bv_solve. }
  unfold withdrawalLoopFacts. repeat split; try assumption.
  - rewrite Hrows -app_assoc /=. reflexivity.
  - rewrite Nat2Z.inj_succ in Hcount |- *. cbn in Hcount. lia.
Qed.
Print Assumptions withdrawal_facts_advance.

Require Import ZesuSsz.Automation.AllLegacy.
Require Import isla.riscv64.riscv64.
From ZesuSsz.Proofs.WriteSuccess Require Import
  WriteSuccessExactWithdrawalsLoopSpec.

Lemma withdrawal_facts_end_pointer sp pointer base rows prefix row source :
  withdrawalLoopFacts sp pointer base rows prefix row [] source ->
  (pointer + BV 64 48)%bv = Z_to_bv 64 (base + Z.of_nat (length source)).
Proof.
  intros Hfacts.
  pose proof (withdrawal_facts_layout sp pointer base rows prefix row [] source Hfacts)
    as (Hprefix & Hrow & Hslice & Hlength).
  destruct Hfacts as (Hrows & Hall & Hbytes & Hposition & Hcount & Halign & Hlow & Hhigh & Hbase & Hend).
  apply (f_equal Z.of_nat) in Hlength.
  rewrite Nat2Z.inj_mul Nat2Z.inj_add in Hlength. cbn in Hlength. bv_solve.
Qed.
Print Assumptions withdrawal_facts_end_pointer.
