From Coq Require Import Lists.List.
Require Import isla.riscv64.riscv64.

Require Import ZesuSsz.Experiments.WriteSuccessTraceAssumptions.
Require Import ZesuSsz.Experiments.WriteSuccessTraceAssumptionsChunk05.
Require Import ZesuSsz.Experiments.WriteSuccessOperationalModel.
Require Import ZesuSsz.Contracts.Level1.
Require Import ZesuSsz.Experiments.WriteSuccessObservation.
Require Import ZesuSsz.Experiments.WriteSuccessConcreteRepresentation.

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

Definition writeSuccessConcreteSetX9Zero
    (state : WriteSuccessConcreteState) : WriteSuccessConcreteState :=
  ((state.1.1 <| seq_regs :=
    <["x9" := RVal_Bits (BV 64 0)]> state.1.1.(seq_regs) |>, state.1.2),
   state.2).

Definition writeSuccessConcretePreTraceEntry
    (args : WriteSuccessArgs WriteSuccessObservation)
    (state : WriteSuccessConcreteState) : Prop :=
  state.2 = [] /\
  writeSuccessConcretePc state = Some 0x14d30 /\
  writeSuccessConcreteInitialState args state.1 /\
  writeSuccessConcreteRepresentation
    (successDecoded WriteSuccessObservation args) state.1.2.(seq_mem)
    (successDecodedAddress WriteSuccessObservation args).

Lemma writeSuccessConcreteInitialStateSetX9Zero args state :
  writeSuccessConcreteInitialState args state.1 ->
  writeSuccessConcreteInitialState args (writeSuccessConcreteSetX9Zero state).1.
Proof.
  intros (Htrace & HpcReg & Hnb & Hinstruction & Htable & Hpc & Hx1 & Hx2 &
    Hx10 & Habi & Hsys & Hreturn & Halign & HstackLow & HstackHigh &
    Hstack & Hmmio).
  unfold writeSuccessConcreteInitialState, writeSuccessConcreteSetX9Zero.
  cbn. repeat split; try assumption.
  - rewrite lookup_insert_ne; [exact Hpc|done].
  - rewrite lookup_insert_ne; [exact Hx1|done].
  - rewrite lookup_insert_ne; [exact Hx2|done].
  - rewrite lookup_insert_ne; [exact Hx10|done].
  - apply List.Forall_forall.
    intros name Hname.
    unfold writeSuccessConcreteRegister64 in Habi |- *.
    destruct (decide (name = "x9")) as [->|Hne].
    + exists (BV 64 0). apply lookup_insert.
    + rewrite lookup_insert_ne; last done.
      rewrite List.Forall_forall in Habi. apply Habi. exact Hname.
  - apply List.Forall_forall.
    intros [kind shape] Hitem.
    rewrite List.Forall_forall in Hsys.
    specialize (Hsys (kind, shape) Hitem).
    destruct kind as [name|root field]; last exact Hsys.
    cbn in Hsys |- *. destruct Hsys as (value & Hlookup & Hshape).
    exists value. split; last exact Hshape.
    rewrite lookup_insert_ne; first exact Hlookup.
    intro Heq. subst name. cbn in Hitem. intuition congruence.
Qed.

Lemma writeSuccessConcretePreTraceEntrySetX9Zero args state :
  writeSuccessConcretePreTraceEntry args state ->
  writeSuccessConcretePreTraceEntry args (writeSuccessConcreteSetX9Zero state).
Proof.
  intros (Hlog & Hpc & Hinitial & Hrepresentation).
  unfold writeSuccessConcretePreTraceEntry.
  refine (conj Hlog (conj _ (conj _ Hrepresentation))).
  - pose proof Hinitial as HinitialFields.
    unfold writeSuccessConcreteInitialState in HinitialFields.
    destruct HinitialFields as (_ & HpcReg & _).
    unfold writeSuccessConcretePc in Hpc |- *.
    unfold writeSuccessConcreteSetX9Zero. cbn. rewrite HpcReg.
    rewrite HpcReg in Hpc.
    rewrite lookup_insert_ne; [exact Hpc|done].
  - apply writeSuccessConcreteInitialStateSetX9Zero. exact Hinitial.
Qed.

Lemma writeSuccessConcretePreTraceEntryDoesNotImplyTraceAssumptions args state :
  writeSuccessConcretePreTraceEntry args state ->
  exists counterexample,
    writeSuccessConcretePreTraceEntry args counterexample /\
    ~ writeSuccessTraceAssumptions counterexample.1.
Proof.
  intro Hentry.
  exists (writeSuccessConcreteSetX9Zero state). split.
  - apply writeSuccessConcretePreTraceEntrySetX9Zero. exact Hentry.
  - apply writeSuccessTraceAssumptionsRejectX9Zero.
    + unfold writeSuccessConcreteSetX9Zero. cbn. apply lookup_insert.
    + destruct Hentry as (_ & _ & Hinitial & _).
      unfold writeSuccessConcreteInitialState in Hinitial.
      destruct Hinitial as
        (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hsys & _).
      rewrite List.Forall_forall in Hsys.
      specialize (Hsys
        (KindReg "rv_ram_base",
          ExactShape (RVal_Bits (BV 64 0x20000000)))).
      specialize (Hsys ltac:(cbn; tauto)).
      cbn in Hsys. destruct Hsys as (value & Hlookup & Hshape).
      subst value. unfold writeSuccessConcreteSetX9Zero. cbn.
      rewrite lookup_insert_ne; done.
Qed.

Print Assumptions writeSuccessTraceX9LowerCollected.
Print Assumptions writeSuccessTraceAssumptionsRejectX9Zero.
Print Assumptions writeSuccessConcreteInitialStateSetX9Zero.
Print Assumptions writeSuccessConcretePreTraceEntrySetX9Zero.
Print Assumptions writeSuccessConcretePreTraceEntryDoesNotImplyTraceAssumptions.
