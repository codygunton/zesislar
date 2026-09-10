From Coq Require Import Lia Lists.List ZArith.ZArith.
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Experiments.WriteSuccessSegment156dc.
Require Import ZesuSsz.Experiments.WriteSuccessSegment156e0.
Require Import ZesuSsz.Experiments.WriteSuccessSegment156e4.
Require Import ZesuSsz.Experiments.WriteSuccessSegment15694.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsOperational.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsOperationalData.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsHandoff156dcLoopTailRecorded.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsRankIndexed.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsRankPosition.

Open Scope Z_scope.

Lemma writeSuccessWithdrawalsTailPosition407 remaining regs global log
    (pointer : bv 64) :
  regs !! "PC" = Some (RVal_Bits (Z_to_bv 64 0x156dc)) ->
  regs !! "x9" = Some (RVal_Bits (Z_to_bv 64 (Z.of_nat (S remaining)))) ->
  (Z.of_nat (S remaining) < 2 ^ 64)%Z ->
  writeSuccessWithdrawalsPositionState remaining 407
    (writeSuccess156dcBefore regs global, log).
Proof.
  intros Hpc Hx9 Hrange. exists 0x156dc. repeat split.
  - unfold writeSuccessWithdrawalsConcretePc, writeSuccess156dcBefore,
      writeSuccess156dcLocal. cbn. rewrite Hpc. unfold bvn_unsigned. cbn.
    rewrite Z_to_bv_unsigned. vm_compute. reflexivity.
  - exact Hx9.
  - discriminate.
  - discriminate.
  - discriminate.
  - discriminate.
  - exact Hrange.
Qed.

Lemma writeSuccessWithdrawalsTailPosition408 remaining regs global log
    (pointer : bv 64) :
  regs !! "PC" = Some (RVal_Bits (Z_to_bv 64 0x156dc)) ->
  regs !! "x9" = Some (RVal_Bits (Z_to_bv 64 (Z.of_nat (S remaining)))) ->
  (Z.of_nat (S remaining) < 2 ^ 64)%Z ->
  writeSuccessWithdrawalsPositionState remaining 408
    (writeSuccess156e0Before (writeSuccess156dcRegs regs pointer) global, log).
Proof.
  intros Hpc Hx9 Hrange. exists 0x156e0. repeat split.
  - unfold writeSuccessWithdrawalsConcretePc, writeSuccess156e0Before,
      writeSuccess156dcRegs, writeSuccess156e0Local. cbn.
    rewrite lookup_insert writeSuccess156dcNextPcExact.
    unfold bvn_unsigned. cbn. rewrite Z_to_bv_unsigned. vm_compute. reflexivity.
  - unfold writeSuccess156e0Before, writeSuccess156e0Local. cbn.
    rewrite writeSuccess156dcRegsLookupOther; try discriminate. exact Hx9.
  - discriminate.
  - discriminate.
  - discriminate.
  - discriminate.
  - exact Hrange.
Qed.

Lemma writeSuccessWithdrawalsTailPosition409 remaining regs global log
    (pointer : bv 64) :
  regs !! "PC" = Some (RVal_Bits (Z_to_bv 64 0x156dc)) ->
  regs !! "x9" = Some (RVal_Bits (Z_to_bv 64 (Z.of_nat (S remaining)))) ->
  (Z.of_nat remaining < 2 ^ 64)%Z ->
  writeSuccessWithdrawalsTerminalPositionState remaining
    (writeSuccess156e4Before
      (writeSuccess156e0Regs (writeSuccess156dcRegs regs pointer)
        (Z_to_bv 64 (Z.of_nat (S remaining)))) global, log).
Proof.
  intros Hpc Hx9 Hrange. repeat split.
  - unfold writeSuccessWithdrawalsConcretePc, writeSuccess156e4Before,
      writeSuccess15694Local, writeSuccess156e0Regs. cbn.
    rewrite lookup_insert writeSuccess156e0NextPcExact.
    unfold bvn_unsigned. cbn. rewrite Z_to_bv_unsigned. vm_compute. reflexivity.
  - unfold writeSuccess156e4Before, writeSuccess15694Local. cbn.
    unfold writeSuccess156e0Regs. rewrite lookup_insert_ne; last discriminate.
    rewrite lookup_insert writeSuccessWithdrawalsCounterDecrementS. reflexivity.
  - exact Hrange.
Qed.

Lemma writeSuccessWithdrawalsTailPosition410 remaining regs global log
    (pointer : bv 64) :
  (Z.of_nat remaining < 2 ^ 64)%Z ->
  let beforeRegs := writeSuccess156e0Regs (writeSuccess156dcRegs regs pointer)
    (Z_to_bv 64 (Z.of_nat (S remaining))) in
  let state :=
    (writeSuccess156e4After (Z_to_bv 64 (Z.of_nat remaining)) beforeRegs global,
     log) in
  writeSuccessWithdrawalsConcretePc state =
    Some (if remaining is O then 0x156e8 else 0x15694) /\
  state.1.1.(seq_regs) !! "x9" =
    Some (RVal_Bits (Z_to_bv 64 (Z.of_nat remaining))).
Proof.
  intros Hrange beforeRegs state. split.
  - unfold state, writeSuccessWithdrawalsConcretePc, writeSuccess156e4After,
      writeSuccess156e4FallthroughAfter, writeSuccess156e4TakenAfter,
      writeSuccess15694Local.
    destruct remaining as [|remaining].
    + cbn. rewrite lookup_insert.
      unfold bvn_unsigned. cbn.
      rewrite Z_to_bv_unsigned. vm_compute. reflexivity.
    + have Hnonzero : Z_to_bv 64 (Z.of_nat (S remaining)) <> BV 64 0.
      { intro Heq. apply bv_eq in Heq. cbn in Heq.
        rewrite Z_to_bv_unsigned in Heq.
        rewrite bv_wrap_small in Heq; first discriminate.
        unfold bv_modulus. cbn in Hrange |- *. lia. }
      rewrite decide_False; last exact Hnonzero. cbn. rewrite lookup_insert.
      destruct writeSuccess156e4PcValues as (_ & Htaken). rewrite Htaken.
      unfold bvn_unsigned. cbn.
      rewrite Z_to_bv_unsigned. rewrite bv_wrap_small; first reflexivity.
      unfold bv_modulus. cbn in Hrange |- *. lia.
  - unfold state. rewrite writeSuccess156e4AfterRegs.
    rewrite writeSuccess156e4RegsLookupOther; last discriminate.
    unfold beforeRegs, writeSuccess156e0Regs.
    rewrite lookup_insert_ne; last discriminate. rewrite lookup_insert.
    rewrite writeSuccessWithdrawalsCounterDecrementS. reflexivity.
Qed.

Print Assumptions writeSuccessWithdrawalsTailPosition407.
Print Assumptions writeSuccessWithdrawalsTailPosition408.
Print Assumptions writeSuccessWithdrawalsTailPosition409.
Print Assumptions writeSuccessWithdrawalsTailPosition410.
