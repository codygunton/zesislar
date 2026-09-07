From Coq Require Import Lia ZArith.ZArith.
Require Import isla.riscv64.riscv64.
Require Import IslaTraces.write_success_07.a15d28.
Require Import IslaTraces.write_success_01.a10190.
Require Import ZesuSsz.Contracts.InstructionBoundary.
Require Import ZesuSsz.Experiments.WriteSuccessSegment15694.
Require Import ZesuSsz.Experiments.WriteSuccessSegment15d28.
Require Import ZesuSsz.Experiments.WriteSuccessSegment15d28Coverage.
Require Import ZesuSsz.Experiments.WriteSuccessTraceAssumptions.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsOperational.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsOperationalData.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsRank.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsRankGeneral.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsRankIndexed.

Open Scope Z_scope.

Lemma writeSuccess15d28PreservesSavedReturn regs global log :
  writeSuccessWithdrawalsSavedReturn (writeSuccess15d28After regs global, log) =
  writeSuccessWithdrawalsSavedReturn (writeSuccess15d28Before regs global, log).
Proof. unfold writeSuccessWithdrawalsSavedReturn,
  writeSuccessWithdrawalsRegisterUnsigned, writeSuccess15d28After,
  writeSuccess15d28Before, writeSuccess15694Local. cbn.
  rewrite writeSuccess15d28RegsLookupOther; try discriminate. reflexivity. Qed.

Lemma writeSuccessOccurrence15d28First state :
  writeSuccessWithdrawalsSavedReturn state = Some 0x156b4 ->
  writeSuccessWithdrawalsSelectedOccurrence state 0x15d28 =
    Some (count_occ Z.eq_dec (firstn (342+11)
      writeSuccessWithdrawalsIterationPcs) 0x15d28).
Proof. intros H. unfold writeSuccessWithdrawalsSelectedOccurrence. rewrite H.
  vm_compute. reflexivity. Qed.

Lemma writeSuccessOccurrence10190First state :
  state.1.1.(seq_regs) !! "x1" = Some (RVal_Bits (Z_to_bv 64 0x15d2c)) ->
  writeSuccessWithdrawalsSavedReturn state = Some 0x156b4 ->
  writeSuccessWithdrawalsSelectedOccurrence state 0x10190 =
    Some (count_occ Z.eq_dec (firstn (342+12)
      writeSuccessWithdrawalsIterationPcs) 0x10190).
Proof. intros Hx1 Hsaved. unfold writeSuccessWithdrawalsSelectedOccurrence,
  writeSuccessWithdrawalsRegisterUnsigned. rewrite Hx1 Hsaved.
  vm_compute. reflexivity. Qed.

Lemma writeSuccessWithdrawals15d28RankDecreases regs global log remaining :
  regs !! "PC" = Some (RVal_Bits (Z_to_bv 64 0x15d28)) ->
  regs !! "x1" = Some (RVal_Bits writeSuccess15d28Ra) ->
  regs !! "x9" = Some (RVal_Bits (Z_to_bv 64 (Z.of_nat (S remaining)))) ->
  writeSuccessWithdrawalsSavedReturn (writeSuccess15d28Before regs global, log) = Some 0x156b4 ->
  (Z.of_nat (S remaining) < 2^64)%Z ->
  rank_15694 (writeSuccess15d28After regs global, log) <
  rank_15694 (writeSuccess15d28Before regs global, log).
Proof.
  intros Hpc Hx1 Hx9 Hsaved Hrange.
  have HpcB : writeSuccessWithdrawalsConcretePc (writeSuccess15d28Before regs global,log)=Some 0x15d28.
  { unfold writeSuccessWithdrawalsConcretePc,writeSuccess15d28Before,writeSuccess15694Local; cbn; rewrite Hpc; reflexivity. }
  have HpcA : writeSuccessWithdrawalsConcretePc (writeSuccess15d28After regs global,log)=Some 0x10190.
  { unfold writeSuccessWithdrawalsConcretePc,writeSuccess15d28After,writeSuccess15694Local,writeSuccess15d28Regs; cbn.
    rewrite lookup_insert. destruct writeSuccess15d28ValuesExact as (_&_&_&H); rewrite H; reflexivity. }
  have Hx9B : (writeSuccess15d28Before regs global).1.(seq_regs)!!"x9"=Some(RVal_Bits(Z_to_bv 64(Z.of_nat(S remaining)))) by exact Hx9.
  have Hx9A : (writeSuccess15d28After regs global).1.(seq_regs)!!"x9"=Some(RVal_Bits(Z_to_bv 64(Z.of_nat(S remaining)))).
  { unfold writeSuccess15d28After,writeSuccess15694Local; cbn. rewrite writeSuccess15d28RegsLookupOther; try discriminate; exact Hx9. }
  have Hx1A : (writeSuccess15d28After regs global).1.(seq_regs)!!"x1"=Some(RVal_Bits(Z_to_bv 64 0x15d2c)).
  { unfold writeSuccess15d28After,writeSuccess15694Local,writeSuccess15d28Regs; cbn. rewrite lookup_insert_ne;last discriminate.
    rewrite lookup_insert. destruct writeSuccess15d28ValuesExact as (_&H&_);rewrite H;reflexivity. }
  have HsavedA : writeSuccessWithdrawalsSavedReturn(writeSuccess15d28After regs global,log)=Some 0x156b4.
  { rewrite writeSuccess15d28PreservesSavedReturn;exact Hsaved. }
  rewrite (writeSuccessWithdrawalsSuffixRankAtIndex _ remaining 11 0x15d28 ltac:(reflexivity) HpcB
    (writeSuccessOccurrence15d28First
      (writeSuccess15d28Before regs global, log) Hsaved)
    Hx9B Hrange ltac:(discriminate) ltac:(discriminate)
    ltac:(discriminate) ltac:(discriminate)).
  rewrite (writeSuccessWithdrawalsSuffixRankAtIndex _ remaining 12 0x10190 ltac:(reflexivity) HpcA
    (writeSuccessOccurrence10190First
      (writeSuccess15d28After regs global, log) Hx1A HsavedA)
    Hx9A Hrange ltac:(discriminate) ltac:(discriminate)
    ltac:(discriminate) ltac:(discriminate)). lia.
Qed.

Lemma writeSuccessWithdrawalsSegment15d28FirstExistsAndDecreases regs global log remaining :
  regs!!"PC"=Some(RVal_Bits(Z_to_bv 64 0x15d28))->regs!!"x1"=Some(RVal_Bits writeSuccess15d28Ra)->
  regs!!"x9"=Some(RVal_Bits(Z_to_bv 64(Z.of_nat(S remaining))))->
  global.(seq_instrs)!!Z_to_bv 64 0x15d28=Some a15d28->global.(seq_instrs)!!Z_to_bv 64 0x10190=Some a10190->
  writeSuccessTraceAssumptions(writeSuccess15d28Before regs global)->
  writeSuccessWithdrawalsSavedReturn(writeSuccess15d28Before regs global,log)=Some 0x156b4->(Z.of_nat(S remaining)<2^64)%Z->
  exists observations after, IslaInstructionSegment(writeSuccess15d28Before regs global) observations after /\
  after=writeSuccess15d28After regs global /\ dom after.1.(seq_regs)=dom regs /\ rank_15694(after,log)<rank_15694(writeSuccess15d28Before regs global,log).
Proof. intros Hpc Hx1 Hx9 Hcode Hnext Hassumptions Hsaved Hrange.
  exists(writeSuccess15d28Observations regs global),(writeSuccess15d28After regs global);split.
  - exact(proj1(segment_15d28 regs global Hpc Hx1 Hcode Hnext Hassumptions)).
  - split;first reflexivity;split.
    + unfold writeSuccess15d28After,writeSuccess15694Local;cbn. apply writeSuccess15d28RegsDom;assumption.
    + eapply writeSuccessWithdrawals15d28RankDecreases;eassumption. Qed.

Lemma writeSuccessWithdrawalsEverySegment15d28FirstDecreases regs global log remaining observations after :
  regs!!"PC"=Some(RVal_Bits(Z_to_bv 64 0x15d28))->regs!!"x1"=Some(RVal_Bits writeSuccess15d28Ra)->
  regs!!"x9"=Some(RVal_Bits(Z_to_bv 64(Z.of_nat(S remaining))))->global.(seq_instrs)!!Z_to_bv 64 0x15d28=Some a15d28->
  global.(seq_instrs)!!Z_to_bv 64 0x10190=Some a10190->writeSuccessTraceAssumptions(writeSuccess15d28Before regs global)->
  writeSuccessWithdrawalsSavedReturn(writeSuccess15d28Before regs global,log)=Some 0x156b4->(Z.of_nat(S remaining)<2^64)%Z->
  IslaInstructionSegment(writeSuccess15d28Before regs global) observations after->after=writeSuccess15d28After regs global /\
  observations=writeSuccess15d28Observations regs global /\ dom after.1.(seq_regs)=dom regs /\ rank_15694(after,log)<rank_15694(writeSuccess15d28Before regs global,log).
Proof. intros Hpc Hx1 Hx9 Hcode Hnext Hassumptions Hsaved Hrange Hsegment.
  destruct(segment_15d28_covered regs global observations after Hpc Hx1 Hcode Hnext Hassumptions Hsegment)as[-> Hobs].
  split;first reflexivity;split;first exact Hobs;split.
  - unfold writeSuccess15d28After,writeSuccess15694Local;cbn. apply writeSuccess15d28RegsDom;assumption.
  - eapply writeSuccessWithdrawals15d28RankDecreases;eassumption. Qed.

Print Assumptions writeSuccess15d28PreservesSavedReturn.
Print Assumptions writeSuccessOccurrence15d28First.
Print Assumptions writeSuccessOccurrence10190First.
Print Assumptions writeSuccessWithdrawals15d28RankDecreases.
Print Assumptions writeSuccessWithdrawalsSegment15d28FirstExistsAndDecreases.
Print Assumptions writeSuccessWithdrawalsEverySegment15d28FirstDecreases.
