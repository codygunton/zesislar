From Coq Require Import Lia Lists.List ZArith.ZArith.
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsOperational.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsOperationalData.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsRank.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsRankGeneral.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsRankIndexed.

Open Scope Z_scope.

Theorem writeSuccessWithdrawalsSuffixRankAdjacent
    before after remaining position pc nextPc :
  nth_error writeSuccessWithdrawalsAfterMemcpyPcs position = Some pc ->
  nth_error writeSuccessWithdrawalsAfterMemcpyPcs (S position) = Some nextPc ->
  writeSuccessWithdrawalsConcretePc before = Some pc ->
  writeSuccessWithdrawalsConcretePc after = Some nextPc ->
  writeSuccessWithdrawalsSelectedOccurrence before pc =
    Some (count_occ Z.eq_dec
      (firstn (342 + position) writeSuccessWithdrawalsIterationPcs) pc) ->
  writeSuccessWithdrawalsSelectedOccurrence after nextPc =
    Some (count_occ Z.eq_dec
      (firstn (342 + S position) writeSuccessWithdrawalsIterationPcs) nextPc) ->
  before.1.1.(seq_regs) !! "x9" =
    Some (RVal_Bits (Z_to_bv 64 (Z.of_nat remaining))) ->
  after.1.1.(seq_regs) !! "x9" =
    Some (RVal_Bits (Z_to_bv 64 (Z.of_nat remaining))) ->
  (0 < remaining)%nat ->
  (Z.of_nat remaining < 2 ^ 64)%Z ->
  pc <> 0x156e4 -> pc <> 0x156e8 -> pc <> 0x1568c -> pc <> 0x15690 ->
  nextPc <> 0x156e4 -> nextPc <> 0x156e8 ->
  nextPc <> 0x1568c -> nextPc <> 0x15690 ->
  rank_15694 after < rank_15694 before.
Proof.
  intros Hposition HnextPosition Hpc HnextPc Hocc HnextOcc Hx9 HnextX9
    Hpositive Hrange HpcE4 HpcE8 Hpc8c Hpc90 HnextE4 HnextE8 Hnext8c Hnext90.
  rewrite (writeSuccessWithdrawalsSuffixRankAtIndex before remaining position pc
    Hposition Hpc Hocc Hx9 Hpositive Hrange HpcE4 HpcE8 Hpc8c Hpc90).
  rewrite (writeSuccessWithdrawalsSuffixRankAtIndex after remaining (S position)
    nextPc HnextPosition HnextPc HnextOcc HnextX9 Hpositive Hrange HnextE4
    HnextE8 Hnext8c Hnext90).
  have Hbound : (S position < 68)%nat.
  { rewrite <- writeSuccessWithdrawalsAfterMemcpyPcsLength.
    apply nth_error_Some. rewrite HnextPosition. discriminate. }
  lia.
Qed.

Theorem writeSuccessWithdrawalsSuffixRankCountChange
    before after remaining position pc :
  nth_error writeSuccessWithdrawalsAfterMemcpyPcs position = Some pc ->
  nth_error writeSuccessWithdrawalsAfterMemcpyPcs (S position) = Some 0x156e4 ->
  writeSuccessWithdrawalsConcretePc before = Some pc ->
  writeSuccessWithdrawalsConcretePc after = Some 0x156e4 ->
  writeSuccessWithdrawalsSelectedOccurrence before pc =
    Some (count_occ Z.eq_dec
      (firstn (342 + position) writeSuccessWithdrawalsIterationPcs) pc) ->
  before.1.1.(seq_regs) !! "x9" =
    Some (RVal_Bits (Z_to_bv 64 (Z.of_nat (S remaining)))) ->
  after.1.1.(seq_regs) !! "x9" =
    Some (RVal_Bits (Z_to_bv 64 (Z.of_nat remaining))) ->
  (Z.of_nat (S remaining) < 2 ^ 64)%Z ->
  pc <> 0x156e4 -> pc <> 0x156e8 -> pc <> 0x1568c -> pc <> 0x15690 ->
  rank_15694 after < rank_15694 before.
Proof.
  intros Hposition HnextPosition Hpc HnextPc Hocc Hx9 HnextX9 Hrange
    HpcE4 HpcE8 Hpc8c Hpc90.
  rewrite (writeSuccessWithdrawalsSuffixRankAtIndex before (S remaining)
    position pc Hposition Hpc Hocc Hx9 (Nat.lt_0_succ remaining) Hrange
    HpcE4 HpcE8 Hpc8c Hpc90).
  unfold rank_15694. rewrite HnextPc.
  unfold writeSuccessWithdrawalsRegisterUnsigned. rewrite HnextX9.
  unfold bvn_unsigned. cbn. rewrite Z_to_bv_unsigned bv_wrap_small.
  - rewrite Nat2Z.id.
    have Hbound : (S position < 68)%nat.
    { rewrite <- writeSuccessWithdrawalsAfterMemcpyPcsLength.
      apply nth_error_Some. rewrite HnextPosition. discriminate. }
    lia.
  - unfold bv_modulus. cbn in Hrange |- *. lia.
Qed.

Theorem writeSuccessWithdrawalsRankEndOfTable
    before after remaining position pc :
  nth_error writeSuccessWithdrawalsAfterMemcpyPcs position = Some pc ->
  (S position = length writeSuccessWithdrawalsAfterMemcpyPcs)%nat ->
  pc = 0x156e4 ->
  writeSuccessWithdrawalsConcretePc before = Some pc ->
  writeSuccessWithdrawalsConcretePc after =
    Some (if remaining is O then 0x156e8 else 0x15694) ->
  before.1.1.(seq_regs) !! "x9" =
    Some (RVal_Bits (Z_to_bv 64 (Z.of_nat remaining))) ->
  after.1.1.(seq_regs) !! "x9" =
    Some (RVal_Bits (Z_to_bv 64 (Z.of_nat remaining))) ->
  (Z.of_nat remaining < 2 ^ 64)%Z ->
  rank_15694 after < rank_15694 before.
Proof.
  intros Hposition Hend -> Hpc HafterPc Hx9 HafterX9 Hrange.
  destruct remaining as [|remaining].
  - unfold rank_15694, writeSuccessWithdrawalsRegisterUnsigned.
    rewrite Hpc HafterPc Hx9 HafterX9. cbn.
    unfold bvn_unsigned. rewrite Z_to_bv_unsigned. cbn.
    rewrite bv_wrap_small.
    + replace (Z.to_nat 0) with 0%nat by reflexivity. cbn. lia.
    + unfold bv_modulus. cbn. lia.
  - unfold rank_15694, writeSuccessWithdrawalsRegisterUnsigned.
    rewrite Hpc HafterPc Hx9 HafterX9. cbn.
    rewrite writeSuccessWithdrawalsPhase15694; last exact HafterPc.
    unfold bvn_unsigned.
    rewrite Z_to_bv_unsigned bv_wrap_small.
    + rewrite Nat2Z.id. cbn. lia.
    + unfold bv_modulus. cbn in Hrange |- *. lia.
Qed.

Theorem writeSuccessWithdrawalsRankPosition409
    before after remaining :
  writeSuccessWithdrawalsConcretePc before = Some 0x156e4 ->
  writeSuccessWithdrawalsConcretePc after =
    Some (if remaining is O then 0x156e8 else 0x15694) ->
  before.1.1.(seq_regs) !! "x9" =
    Some (RVal_Bits (Z_to_bv 64 (Z.of_nat remaining))) ->
  after.1.1.(seq_regs) !! "x9" =
    Some (RVal_Bits (Z_to_bv 64 (Z.of_nat remaining))) ->
  (Z.of_nat remaining < 2 ^ 64)%Z ->
  rank_15694 after < rank_15694 before.
Proof.
  intros Hpc HafterPc Hx9 HafterX9 Hrange.
  eapply (writeSuccessWithdrawalsRankEndOfTable before after remaining 67
    0x156e4); try eassumption; reflexivity.
Qed.

Print Assumptions writeSuccessWithdrawalsSuffixRankAdjacent.
Print Assumptions writeSuccessWithdrawalsSuffixRankCountChange.
Print Assumptions writeSuccessWithdrawalsRankEndOfTable.
Print Assumptions writeSuccessWithdrawalsRankPosition409.
