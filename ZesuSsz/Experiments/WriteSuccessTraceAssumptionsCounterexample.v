From Coq Require Import Lists.List.
Require Import isla.riscv64.riscv64.

Require Import ZesuSsz.Experiments.WriteSuccessTraceAssumptions.
Require Import ZesuSsz.Experiments.WriteSuccessTraceAssumptionsChunk05.

Import ListNotations.

Definition writeSuccessTraceX9LowerCondition : a_exp :=
  AExp_Binop (Bvcomp Bvuge)
    (AExp_Manyop (Bvmanyarith Bvadd)
      [AExp_Val (AVal_Var "x9" []) Mk_annot;
       AExp_Val (AVal_Bits (BV 64 0)) Mk_annot] Mk_annot)
    (AExp_Val (AVal_Var "rv_ram_base" []) Mk_annot) Mk_annot.

Definition writeSuccessTraceX9LowerAssumption : isla_trace :=
  Assume writeSuccessTraceX9LowerCondition Mk_annot :t: tnil.

Lemma writeSuccessTraceX9LowerCollected :
  In writeSuccessTraceX9LowerAssumption
    writeSuccessTraceAssumptionEvents.
Proof.
  unfold writeSuccessTraceX9LowerAssumption,
    writeSuccessTraceX9LowerCondition,
    writeSuccessTraceAssumptionEvents.
  apply in_concat. exists writeSuccessTraceAssumptionsChunk05.
  split.
  - cbn. tauto.
  - unfold writeSuccessTraceAssumptionsChunk05. cbn. tauto.
Qed.

Lemma writeSuccessTraceAssumptionsRejectX9Zero state :
  state.1.(seq_regs) !! "x9" = Some (RVal_Bits (BV 64 0)) ->
  state.1.(seq_regs) !! "rv_ram_base" =
    Some (RVal_Bits (BV 64 0x20000000)) ->
  ~ writeSuccessTraceAssumptions state.
Proof.
  intros Hx9 Hram Hassumptions.
  unfold writeSuccessTraceAssumptions in Hassumptions.
  rewrite List.Forall_forall in Hassumptions.
  specialize (Hassumptions writeSuccessTraceX9LowerAssumption
    writeSuccessTraceX9LowerCollected).
  unfold writeSuccessTraceAssumptionHolds,
    writeSuccessTraceX9LowerAssumption,
    writeSuccessTraceX9LowerCondition in Hassumptions.
  cbn in Hassumptions. rewrite Hx9 Hram in Hassumptions.
  discriminate Hassumptions.
Qed.

Print Assumptions writeSuccessTraceX9LowerCollected.
Print Assumptions writeSuccessTraceAssumptionsRejectX9Zero.
