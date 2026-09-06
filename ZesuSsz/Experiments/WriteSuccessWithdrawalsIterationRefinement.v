From Coq Require Import Lists.List ZArith.ZArith.
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Contracts.InstructionBoundary.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsIteration.

Import ListNotations.

Definition writeSuccessWithdrawalsInsufficientView :
    WriteSuccessWithdrawalsIterationState unit := {|
  writeSuccessIterationPc := 0x15694;
  writeSuccessIterationPointer := 0;
  writeSuccessIterationProcessed := 0;
  writeSuccessIterationRemaining := 2;
  writeSuccessIterationSuffix := [];
  writeSuccessIterationFrame := tt
|}.

Definition writeSuccessWithdrawalsInsufficientRegs : reg_map :=
  <[ "PC" := RVal_Bits (Z_to_bv 64 0x15694) ]> $
  <[ "x8" := RVal_Bits (Z_to_bv 64 0) ]> $
  <[ "x9" := RVal_Bits (Z_to_bv 64 2) ]> $
  ∅.

Definition writeSuccessWithdrawalsInsufficientLocal : seq_local_state := {|
  seq_trace := false_trace;
  seq_regs := writeSuccessWithdrawalsInsufficientRegs;
  seq_pc_reg := "PC";
  seq_nb_state := false
|}.

Definition writeSuccessWithdrawalsInsufficientGlobal : seq_global_state := {|
  seq_instrs := ∅;
  seq_mem := ∅
|}.

Definition writeSuccessWithdrawalsInsufficientState : IslaState :=
  (writeSuccessWithdrawalsInsufficientLocal,
   writeSuccessWithdrawalsInsufficientGlobal).

Lemma writeSuccessWithdrawalsReflectAllowsBlockingState :
  writeSuccessWithdrawalsIterationReflect
    writeSuccessWithdrawalsInsufficientState
    writeSuccessWithdrawalsInsufficientView.
Proof.
  unfold writeSuccessWithdrawalsIterationReflect,
    writeSuccessWithdrawalsInsufficientState,
    writeSuccessWithdrawalsInsufficientLocal,
    writeSuccessWithdrawalsInsufficientGlobal,
    writeSuccessWithdrawalsInsufficientRegs,
    writeSuccessWithdrawalsInsufficientView.
  cbn. repeat split.
Qed.

Lemma writeSuccessWithdrawalsBlockingStateHasNoStep labels local global spawned :
  ~ seq_step writeSuccessWithdrawalsInsufficientLocal
      writeSuccessWithdrawalsInsufficientGlobal labels local global spawned.
Proof.
  intros Hstep. inversion Hstep; subst; cbn in *.
  inversion H0; subst; cbn in *.
  destruct_and!. simplify_eq.
Qed.

Lemma writeSuccessWithdrawalsBlockingStateHasNoSegment observations after :
  ~ IslaInstructionSegment writeSuccessWithdrawalsInsufficientState
      observations after.
Proof.
  intros Hsegment.
  destruct Hsegment as
    [Hboundary done prefix labels spawned Hprefix HatDone Hdone Hobservations Hend].
  inversion Hprefix; subst.
  - discriminate HatDone.
  - eapply writeSuccessWithdrawalsBlockingStateHasNoStep. exact H0.
Qed.

Lemma writeSuccessWithdrawalsReflectDoesNotImplyRun410 :
  writeSuccessWithdrawalsIterationReflect
    writeSuccessWithdrawalsInsufficientState
    writeSuccessWithdrawalsInsufficientView /\
  forall segments after,
    ~ IslaInstructionRun 410 writeSuccessWithdrawalsInsufficientState
        segments after.
Proof.
  split; first apply writeSuccessWithdrawalsReflectAllowsBlockingState.
  intros segments after Hrun. inversion Hrun; subst.
  eapply writeSuccessWithdrawalsBlockingStateHasNoSegment. exact H0.
Qed.

Print Assumptions writeSuccessWithdrawalsReflectAllowsBlockingState.
Print Assumptions writeSuccessWithdrawalsBlockingStateHasNoStep.
Print Assumptions writeSuccessWithdrawalsReflectDoesNotImplyRun410.
