From Coq Require Import Lists.List.
Require Import isla.opsem.
Require Import ZesuSsz.Contracts.InstructionBoundary.
Require Import ZesuSsz.Experiments.WriteSuccessTraceAssumptionsChunk00.
Require Import ZesuSsz.Experiments.WriteSuccessTraceAssumptionsChunk01.
Require Import ZesuSsz.Experiments.WriteSuccessTraceAssumptionsChunk02.
Require Import ZesuSsz.Experiments.WriteSuccessTraceAssumptionsChunk03.
Require Import ZesuSsz.Experiments.WriteSuccessTraceAssumptionsChunk04.
Require Import ZesuSsz.Experiments.WriteSuccessTraceAssumptionsChunk05.
Require Import ZesuSsz.Experiments.WriteSuccessTraceAssumptionsChunk06.
Require Import ZesuSsz.Experiments.WriteSuccessTraceAssumptionsChunk07.
Require Import ZesuSsz.Experiments.WriteSuccessTraceAssumptionsChunk08.
Require Import ZesuSsz.Experiments.WriteSuccessTraceAssumptionsChunk09.
Require Import ZesuSsz.Experiments.WriteSuccessTraceAssumptionsChunk10.
Require Import ZesuSsz.Experiments.WriteSuccessTraceAssumptionsChunk11.
Require Import ZesuSsz.Experiments.WriteSuccessTraceAssumptionsChunk12.
Require Import ZesuSsz.Experiments.WriteSuccessTraceAssumptionsChunk13.
Require Import ZesuSsz.Experiments.WriteSuccessTraceAssumptionsChunk14.
Require Import ZesuSsz.Experiments.WriteSuccessTraceAssumptionsChunk15.
Require Import ZesuSsz.Experiments.WriteSuccessTraceAssumptionsChunk16.

Import ListNotations.

Definition writeSuccessTraceAssumptionEvents : list isla_trace :=
  concat [writeSuccessTraceAssumptionsChunk00; writeSuccessTraceAssumptionsChunk01; writeSuccessTraceAssumptionsChunk02; writeSuccessTraceAssumptionsChunk03; writeSuccessTraceAssumptionsChunk04; writeSuccessTraceAssumptionsChunk05; writeSuccessTraceAssumptionsChunk06; writeSuccessTraceAssumptionsChunk07; writeSuccessTraceAssumptionsChunk08; writeSuccessTraceAssumptionsChunk09; writeSuccessTraceAssumptionsChunk10; writeSuccessTraceAssumptionsChunk11; writeSuccessTraceAssumptionsChunk12; writeSuccessTraceAssumptionsChunk13; writeSuccessTraceAssumptionsChunk14; writeSuccessTraceAssumptionsChunk15; writeSuccessTraceAssumptionsChunk16].

Definition writeSuccessTraceAssumptionHolds
    (regs : reg_map) (assumption : isla_trace) : Prop :=
  match assumption with
  | Assume condition _ :t: tnil =>
      eval_a_exp regs condition = Some (Val_Bool true)
  | AssumeReg register access expected _ :t: tnil =>
      exists root, regs !! register = Some root /\
        read_accessor access root = Some expected
  | _ => False
  end.

Definition writeSuccessTraceAssumptions (state : IslaState) : Prop :=
  Forall (writeSuccessTraceAssumptionHolds state.1.(seq_regs))
    writeSuccessTraceAssumptionEvents.

Lemma writeSuccessTraceAssumptionEventsCount :
  length writeSuccessTraceAssumptionEvents = 834%nat.
Proof.
  unfold writeSuccessTraceAssumptionEvents,
    writeSuccessTraceAssumptionsChunk00, writeSuccessTraceAssumptionsChunk01, writeSuccessTraceAssumptionsChunk02, writeSuccessTraceAssumptionsChunk03, writeSuccessTraceAssumptionsChunk04, writeSuccessTraceAssumptionsChunk05, writeSuccessTraceAssumptionsChunk06, writeSuccessTraceAssumptionsChunk07, writeSuccessTraceAssumptionsChunk08, writeSuccessTraceAssumptionsChunk09, writeSuccessTraceAssumptionsChunk10, writeSuccessTraceAssumptionsChunk11, writeSuccessTraceAssumptionsChunk12, writeSuccessTraceAssumptionsChunk13, writeSuccessTraceAssumptionsChunk14, writeSuccessTraceAssumptionsChunk15, writeSuccessTraceAssumptionsChunk16.
  reflexivity.
Qed.

Print Assumptions writeSuccessTraceAssumptionEventsCount.
