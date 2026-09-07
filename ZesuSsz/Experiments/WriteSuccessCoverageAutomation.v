From Coq Require Import Lists.List.
Require Import isla.opsem.
Require Import ZesuSsz.Contracts.InstructionBoundary.

Lemma writeSuccessInstructionPrefixAllNonblocking before observations done :
  IslaInstructionPrefixPath before observations done ->
  done.1.(seq_nb_state) = false ->
  Forall (fun observation =>
    observation.(microAfter).1.(seq_nb_state) = false) observations.
Proof.
  intros Hpath. induction Hpath.
  - intros _. constructor.
  - intros Hdone. constructor.
    + destruct observations as [|next rest].
      * inversion Hpath; subst. exact Hdone.
      * inversion Hpath; subst.
        eapply seqStepSourceBlocking. exact H5.
    + apply IHHpath. exact Hdone.
Qed.

Lemma writeSuccessInstructionSegmentPrefixAllNonblocking
    before observations after :
  IslaInstructionSegment before observations after ->
  exists prefix doneObservation,
    observations = prefix ++ [doneObservation] /\
    Forall (fun observation =>
      observation.(microAfter).1.(seq_nb_state) = false) prefix.
Proof.
  intros Hsegment.
  destruct Hsegment as
    [Hstart done prefix labels spawned Hprefix Hnil Hstep -> Hend].
  exists prefix,
    {| microLabels := labels; microAfter := after |}.
  split; first reflexivity.
  eapply writeSuccessInstructionPrefixAllNonblocking; first exact Hprefix.
  eapply seqStepSourceBlocking. exact Hstep.
Qed.

Ltac writeSuccessRejectBlockingPrefix Hsegment :=
  let prefix := fresh "prefix" in
  let doneObservation := fresh "doneObservation" in
  let Hobservations := fresh "Hobservations" in
  let Hnonblocking := fresh "Hnonblocking" in
  destruct (writeSuccessInstructionSegmentPrefixAllNonblocking
    _ _ _ Hsegment) as
    (prefix & doneObservation & Hobservations & Hnonblocking).

Lemma writeSuccessDoneTabledCovered local global labels afterLocal afterGlobal
    spawned (pc : bv 64) trace :
  local.(seq_trace) = tnil ->
  local.(seq_regs) !! local.(seq_pc_reg) = Some (RVal_Bits pc) ->
  global.(seq_instrs) !! pc = Some trace ->
  seq_step local global labels afterLocal afterGlobal spawned ->
  labels = [] /\
  afterLocal = local <| seq_trace := trace |> /\
  afterGlobal = global /\
  spawned = [].
Proof.
  intros Hnil Hpc Htable Hstep.
  inversion Hstep as
    [stepGlobal stepLocal event next event' nextLocal nextGlobal
      Hnb Htrace Hsem]; subst.
  rewrite Hnil in Htrace. inversion Htrace; subst.
  cbn in Hsem. destruct Hsem as (-> & found & Hfound & Hresult).
  rewrite Hpc in Hfound. simplify_eq.
  rewrite Htable in Hresult.
  destruct Hresult as (-> & Heq & ->). subst next.
  repeat split; reflexivity.
Qed.

Lemma writeSuccessDoneTrapCovered local global labels afterLocal afterGlobal
    spawned (pc : bv 64) :
  local.(seq_trace) = tnil ->
  local.(seq_regs) !! local.(seq_pc_reg) = Some (RVal_Bits pc) ->
  global.(seq_instrs) !! pc = None ->
  seq_step local global labels afterLocal afterGlobal spawned ->
  labels = [SInstrTrap pc] /\
  afterLocal = local <| seq_nb_state := true |> /\
  afterGlobal = global /\
  spawned = [].
Proof.
  intros Hnil Hpc Htable Hstep.
  inversion Hstep as
    [stepGlobal stepLocal event next' event' nextLocal nextGlobal
      Hnb Htrace Hsem]; subst.
  rewrite Hnil in Htrace. inversion Htrace; subst.
  cbn in Hsem. destruct Hsem as (-> & found & Hfound & Hresult).
  rewrite Hpc in Hfound. simplify_eq.
  rewrite Htable in Hresult. destruct Hresult as (-> & ->).
  repeat split; reflexivity.
Qed.

Print Assumptions writeSuccessInstructionPrefixAllNonblocking.
Print Assumptions writeSuccessInstructionSegmentPrefixAllNonblocking.
Print Assumptions writeSuccessDoneTabledCovered.
Print Assumptions writeSuccessDoneTrapCovered.
