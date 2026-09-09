From Coq Require Import Lia Lists.List ZArith.ZArith.
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Contracts.IslaMemoryOperational.
Require Import ZesuSsz.Experiments.WriteSuccessObservation.
Require Import ZesuSsz.Experiments.WriteSuccessConcreteRepresentation.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsOperational.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsRepresentationBlocker.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsRepresentationBlockerData.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsRepresentationBlockerLists.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsIterationStatementBlockerState.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsIterationStatementBlockerMachine.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsIterationStatementBlockerMemory.

Import ListNotations.
Open Scope Z_scope.

Local Opaque writeSuccessBlockerLocal writeSuccessBlockerGlobal
  writeSuccessBlockerRegs writeSuccessBlockerRepresentedMemory.

Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsIterationStatementBlockerItems.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsIterationStatementBlockerReads.

Lemma writeSuccessBlockerInv15694 :
  Inv_15694 writeSuccessBlockerArgs writeSuccessBlockerSp
    writeSuccessBlockerPointer 0x20001000 2 0 2
    writeSuccessBlockerWithdrawal writeSuccessBlockerAllBytes []
    writeSuccessBlockerCurrent writeSuccessBlockerNext
    writeSuccessBlockerScratchBefore writeSuccessBlockerEncoderScratch
    writeSuccessBlockerRegs writeSuccessBlockerRepresentedMemory []
    writeSuccessBlockerState.
Proof.
  unfold Inv_15694. cbn [writeSuccessBlockerState].
  split; [exact writeSuccessBlockerBoundary|].
  split; [exact writeSuccessBlockerLocalPcReg|].
  split; [exact writeSuccessBlockerConcretePc|].
  rewrite !writeSuccessBlockerLocalRegs
    !writeSuccessBlockerGlobalMemory.
  destruct writeSuccessBlockerEntryRegisterLookups as
    (Hx1 & Hx2 & Hx10 & Hx11 & Hx12 & Hx15 & Hx8 & Hx9 & Hx18).
  split; [exact Hx1|].
  split; [exact Hx2|].
  split; [exact Hx10|].
  split; [exact Hx11|].
  split; [exact Hx12|].
  split; [exact Hx15|].
  split; [exact Hx8|].
  split; [exact Hx9|].
  split; [exact Hx18|].
  split; [exact writeSuccessBlockerRegisterFrame|].
  split; [exact writeSuccessBlockerMemoryFrame|].
  split; [exact writeSuccessBlockerInstructionTable|].
  split; [exact writeSuccessBlockerRegisterFacts|].
  split; [exact writeSuccessBlockerFullRepresentation|].
  split; [exact writeSuccessBlockerWithdrawalItems|].
  split; [reflexivity|].
  split; [reflexivity|].
  split; [reflexivity|].
  split; [reflexivity|].
  split; [reflexivity|].
  split; [reflexivity|].
  split; [reflexivity|].
  split; [reflexivity|].
  split; [reflexivity|].
  split; [change (536870912 <= 536875008 - 16); lia|].
  split; [change (536875008 + 1792 < 1073741824); lia|].
  split; [change (536870912 <= 536875008); lia|].
  split.
  { change (536875008 + Z.of_nat (length writeSuccessBlockerAllBytes) <
      1073741824).
    unfold writeSuccessBlockerAllBytes, writeSuccessBlockerCurrent,
      writeSuccessBlockerNext. cbn. lia. }
  split; [change (536875008 = 536875008 + 48 * Z.of_nat 0); lia|].
  split; [exact writeSuccessBlockerAllBytesRead|].
  split; [exact writeSuccessBlockerCurrentRead|].
  split.
  { pose proof writeSuccessBlockerWithdrawalItems as Hitems.
    unfold writeSuccessWithdrawalItemsAt in Hitems.
    exact (Hitems O
      writeSuccessBlockerWithdrawal eq_refl). }
  split; [exact writeSuccessBlockerScratchRead|].
  split; [exact writeSuccessBlockerEncoderScratchRead|].
  split.
  { unfold islaMemoryRangesDisjoint, writeSuccessBlockerPointer,
      writeSuccessBlockerSp. cbn. left. lia. }
  split.
  { unfold islaMemoryRangesDisjoint.
    rewrite writeSuccessBlockerSpUnsigned.
    unfold writeSuccessBlockerAllBytes, writeSuccessBlockerCurrent,
      writeSuccessBlockerNext. cbn. right. lia. }
  split.
  { unfold islaMemoryRangesDisjoint.
    rewrite writeSuccessBlockerSpUnsigned.
    unfold writeSuccessBlockerAllBytes, writeSuccessBlockerCurrent,
      writeSuccessBlockerNext. cbn. left. lia. }
  split.
  { change (set_Forall writeSuccessBlockerOutsideMmio
      (dom writeSuccessBlockerRepresentedMemory)).
    exact writeSuccessBlockerNoMmioMemory. }
  reflexivity.
Qed.

Print Assumptions writeSuccessBlockerInv15694.
