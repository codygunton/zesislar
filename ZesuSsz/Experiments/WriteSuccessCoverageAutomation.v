From Coq Require Import Eqdep_dec Lists.List NArith.NArith.
Require Import isla.opsem.
Require Import ZesuSsz.Contracts.InstructionBoundary.

Lemma writeSuccessBvToBvnInjective n (left right : bv n) :
  bv_to_bvn left = bv_to_bvn right -> left = right.
Proof.
  intro Heq. injection Heq as Hsigma.
  exact (inj_pair2_eq_dec N (Coq.NArith.BinNat.N.eq_dec)
    (fun width => bv width) n left right Hsigma).
Qed.

Lemma writeSuccessBitsValInjective n (left right : bv n) :
  RVal_Bits (bv_to_bvn left) = RVal_Bits (bv_to_bvn right) -> left = right.
Proof.
  intro Heq. injection Heq as Heq.
  exact (inj_pair2_eq_dec N (Coq.NArith.BinNat.N.eq_dec)
    (fun width => bv width) n left right Heq).
Qed.

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

Lemma writeSuccessReadRegCovered local global labels afterLocal afterGlobal
    spawned register access symbolic annotation trace' root value :
  local.(seq_trace) =
    ReadReg register access symbolic annotation :t: trace' ->
  local.(seq_regs) !! register = Some root ->
  read_accessor access root = Some value ->
  read_accessor access symbolic = Some value ->
  afterLocal.(seq_nb_state) = false ->
  seq_step local global labels afterLocal afterGlobal spawned ->
  labels = [] /\
  afterLocal = local <| seq_trace := trace' |> /\
  afterGlobal = global /\
  spawned = [].
Proof.
  intros Hsource Hregister Hroot Hsymbolic Hafter Hstep.
  inversion Hstep as
    [stepGlobal stepLocal event next event' nextLocal nextGlobal
      Hnb Htrace Hsem]; subst.
  rewrite Hsource in Htrace. inversion Htrace; subst.
  cbn in Hsem.
  destruct Hsem as
    (actualRoot & actualValue & symbolicValue & Hregister' & -> &
     Hactual & Hsymbolic' & -> & Hsuccess).
  rewrite Hregister in Hregister'. inversion Hregister'; subst.
  rewrite Hroot in Hactual. inversion Hactual; subst.
  rewrite Hsymbolic in Hsymbolic'. inversion Hsymbolic'; subst.
  destruct Hsuccess as [(-> & _)|Hblock].
  - repeat split; reflexivity.
  - subst. discriminate Hafter.
Qed.

Lemma writeSuccessAssumeCovered local global labels afterLocal afterGlobal
    spawned expression annotation trace' :
  local.(seq_trace) = Assume expression annotation :t: trace' ->
  eval_a_exp local.(seq_regs) expression = Some (Val_Bool true) ->
  seq_step local global labels afterLocal afterGlobal spawned ->
  labels = [] /\
  afterLocal = local <| seq_trace := trace' |> <| seq_nb_state := false |> /\
  afterGlobal = global /\
  spawned = [].
Proof.
  intros Hsource Heval Hstep.
  inversion Hstep as
    [stepGlobal stepLocal event next event' nextLocal nextGlobal
      Hnb Htrace Hsem]; subst.
  rewrite Hsource in Htrace. inversion Htrace; subst.
  cbn in Hsem. destruct Hsem as (-> & -> & _ & ->).
  repeat split; reflexivity.
Qed.

Lemma writeSuccessDefineConstCovered local global labels afterLocal afterGlobal
    spawned identifier expression annotation trace' value :
  local.(seq_trace) =
    Smt (DefineConst identifier expression) annotation :t: trace' ->
  eval_exp expression = Some value ->
  seq_step local global labels afterLocal afterGlobal spawned ->
  labels = [] /\
  afterLocal = local <| seq_trace :=
    subst_trace value identifier trace' |> /\
  afterGlobal = global /\
  spawned = [].
Proof.
  intros Hsource Heval Hstep.
  inversion Hstep as
    [stepGlobal stepLocal event next event' nextLocal nextGlobal
      Hnb Htrace Hsem]; subst.
  rewrite Hsource in Htrace. inversion Htrace; subst.
  match goal with
  | Hactual : eval_exp expression = Some ?actual |- _ =>
      rewrite Heval in Hactual; inversion Hactual; subst actual
  end.
  cbn in Hsem. destruct Hsem as (-> & -> & ->).
  repeat split; reflexivity.
Qed.

Lemma writeSuccessAssertCovered local global labels afterLocal afterGlobal
    spawned expression annotation trace' :
  local.(seq_trace) =
    Smt (Assert expression) annotation :t: trace' ->
  eval_exp expression = Some (Val_Bool true) ->
  afterLocal.(seq_nb_state) = false ->
  seq_step local global labels afterLocal afterGlobal spawned ->
  labels = [] /\
  afterLocal = local <| seq_trace := trace' |> <| seq_nb_state := false |> /\
  afterGlobal = global /\
  spawned = [].
Proof.
  intros Hsource Heval Hafter Hstep.
  inversion Hstep as
    [stepGlobal stepLocal event next event' nextLocal nextGlobal
      Hnb Htrace Hsem]; subst.
  rewrite Hsource in Htrace. inversion Htrace; subst.
  cbn in Hsem. destruct Hsem as (-> & -> & ->).
  destruct b; cbn in *; try discriminate.
  repeat split; reflexivity.
Qed.

Lemma writeSuccessAssumeRegCovered local global labels afterLocal afterGlobal
    spawned register access expected annotation trace' root :
  local.(seq_trace) =
    AssumeReg register access expected annotation :t: trace' ->
  local.(seq_regs) !! register = Some root ->
  read_accessor access root = Some expected ->
  seq_step local global labels afterLocal afterGlobal spawned ->
  labels = [] /\
  afterLocal = local <| seq_trace := trace' |> /\
  afterGlobal = global /\
  spawned = [].
Proof.
  intros Hsource Hregister Haccess Hstep.
  inversion Hstep as
    [stepGlobal stepLocal event next event' nextLocal nextGlobal
      Hnb Htrace Hsem]; subst.
  rewrite Hsource in Htrace. inversion Htrace; subst.
  cbn in Hsem.
  destruct Hsem as (actualRoot & Hregister' & -> & Haccess' & -> & ->).
  rewrite Hregister in Hregister'. inversion Hregister'; subst.
  rewrite Haccess in Haccess'. inversion Haccess'.
  repeat split; reflexivity.
Qed.

Lemma writeSuccessWriteRegCovered local global labels afterLocal afterGlobal
    spawned register access symbolic annotation trace' root value updated :
  local.(seq_trace) =
    WriteReg register access symbolic annotation :t: trace' ->
  local.(seq_regs) !! register = Some root ->
  read_accessor access symbolic = Some value ->
  write_accessor access root value = Some updated ->
  seq_step local global labels afterLocal afterGlobal spawned ->
  labels = [] /\
  afterLocal = local <| seq_trace := trace' |>
    <| seq_regs := <[register := updated]> local.(seq_regs) |> /\
  afterGlobal = global /\
  spawned = [].
Proof.
  intros Hsource Hregister Hread Hwrite Hstep.
  inversion Hstep as
    [stepGlobal stepLocal event next event' nextLocal nextGlobal
      Hnb Htrace Hsem]; subst.
  rewrite Hsource in Htrace. inversion Htrace; subst.
  cbn in Hsem.
  destruct Hsem as
    (actualRoot & actualUpdated & actualValue & Hregister' & Hread' &
     Hwrite' & -> & -> & ->).
  rewrite Hregister in Hregister'. inversion Hregister'; subst.
  rewrite Hread in Hread'. inversion Hread'; subst.
  rewrite Hwrite in Hwrite'. inversion Hwrite'; subst.
  repeat split; reflexivity.
Qed.

Lemma writeSuccessBranchAddressCovered local global labels afterLocal afterGlobal
    spawned target annotation trace' :
  local.(seq_trace) = BranchAddress target annotation :t: trace' ->
  seq_step local global labels afterLocal afterGlobal spawned ->
  labels = [] /\
  afterLocal = local <| seq_trace := trace' |> /\
  afterGlobal = global /\
  spawned = [].
Proof.
  intros Hsource Hstep.
  inversion Hstep as
    [stepGlobal stepLocal event next event' nextLocal nextGlobal
      Hnb Htrace Hsem]; subst.
  rewrite Hsource in Htrace. inversion Htrace; subst.
  cbn in Hsem. destruct Hsem as (-> & -> & ->).
  repeat split; reflexivity.
Qed.

Lemma writeSuccessBranchCovered local global labels afterLocal afterGlobal
    spawned condition description annotation trace' :
  local.(seq_trace) =
    Branch condition description annotation :t: trace' ->
  seq_step local global labels afterLocal afterGlobal spawned ->
  labels = [] /\
  afterLocal = local <| seq_trace := trace' |> /\
  afterGlobal = global /\
  spawned = [].
Proof.
  intros Hsource Hstep.
  inversion Hstep as
    [stepGlobal stepLocal event next event' nextLocal nextGlobal
      Hnb Htrace Hsem]; subst.
  rewrite Hsource in Htrace. inversion Htrace; subst.
  cbn in Hsem. destruct Hsem as (-> & -> & ->).
  repeat split; reflexivity.
Qed.

Lemma writeSuccessReadMemBackedCovered local global labels afterLocal afterGlobal
    spawned trace' kind (address : bv 64) len tag
    (value : bv (8 * len)) :
  local.(seq_trace) =
    ReadMem (RVal_Bits (bv_to_bvn value)) kind
      (RVal_Bits (bv_to_bvn address)) len tag Mk_annot :t: trace' ->
  (0 < Z.of_N len)%Z ->
  read_mem global.(seq_mem) (bv_unsigned address) len =
    Some (bv_to_bvn value) ->
  afterLocal.(seq_nb_state) = false ->
  seq_step local global labels afterLocal afterGlobal spawned ->
  labels = [] /\
  afterLocal = local <| seq_trace := trace' |> /\
  afterGlobal = global /\
  spawned = [].
Proof.
  intros Hsource Hlen Hread Hafter Hstep.
  inversion Hstep as
    [stepGlobal stepLocal event next event' nextLocal nextGlobal
      Hnb Htrace Hsem]; subst.
  rewrite Hsource in Htrace. inversion Htrace; subst.
  cbn in Hsem.
  destruct Hsem as (actualAddress & actualValue & memoryValue & Hsem).
  destruct Hsem as [Haddress Hsem].
  destruct Hsem as [Hvalue Hsem].
  destruct Hsem as [Hlen' Hbranch].
  apply writeSuccessBitsValInjective in Haddress. subst actualAddress.
  apply writeSuccessBitsValInjective in Hvalue. subst actualValue.
  rewrite Hread in Hbranch.
  destruct Hbranch as (Hmemory & -> & -> & Hsuccess).
  assert (HmemoryValue : bv_to_bvn value = bv_to_bvn memoryValue)
    by congruence.
  apply writeSuccessBvToBvnInjective in HmemoryValue. subst memoryValue.
  destruct Hsuccess as [(-> & _)|Hblock].
  - repeat split; reflexivity.
  - subst. discriminate Hafter.
Qed.

Lemma writeSuccessReadMemMmioCovered local global labels afterLocal afterGlobal
    spawned trace' kind (address : bv 64) len tag
    (value : bv (8 * len)) :
  local.(seq_trace) =
    ReadMem (RVal_Bits (bv_to_bvn value)) kind
      (RVal_Bits (bv_to_bvn address)) len tag Mk_annot :t: trace' ->
  (0 < Z.of_N len)%Z ->
  read_mem global.(seq_mem) (bv_unsigned address) len = None ->
  seq_step local global labels afterLocal afterGlobal spawned ->
  labels = [SReadMem address (bv_to_bvn value)] /\
  afterLocal = local <| seq_trace := trace' |> /\
  afterGlobal = global /\
  spawned = [].
Proof.
  intros Hsource Hlen Hread Hstep.
  inversion Hstep as
    [stepGlobal stepLocal event next event' nextLocal nextGlobal
      Hnb Htrace Hsem]; subst.
  rewrite Hsource in Htrace. inversion Htrace; subst.
  cbn in Hsem.
  destruct Hsem as (actualAddress & actualValue & ignoredValue & Hsem).
  destruct Hsem as [Haddress Hsem].
  destruct Hsem as [Hvalue Hsem].
  destruct Hsem as [Hlen' Hbranch].
  apply writeSuccessBitsValInjective in Haddress. subst actualAddress.
  apply writeSuccessBitsValInjective in Hvalue. subst actualValue.
  rewrite Hread in Hbranch.
  destruct Hbranch as (_ & _ & -> & -> & ->).
  repeat split; reflexivity.
Qed.

Lemma writeSuccessWriteMemBackedCovered local global labels afterLocal afterGlobal
    spawned trace' result kind (address : bv 64) len tag
    (value : bv (8 * len)) old :
  local.(seq_trace) =
    WriteMem result kind (RVal_Bits (bv_to_bvn address))
      (RVal_Bits (bv_to_bvn value)) len tag Mk_annot :t: trace' ->
  (0 < Z.of_N len)%Z ->
  read_mem global.(seq_mem) (bv_unsigned address) len = Some old ->
  seq_step local global labels afterLocal afterGlobal spawned ->
  labels = [] /\
  afterLocal = local <| seq_trace := trace' |> /\
  afterGlobal = global <| seq_mem :=
    write_mem len global.(seq_mem) address (bv_unsigned value) |> /\
  spawned = [].
Proof.
  intros Hsource Hlen Hread Hstep.
  inversion Hstep as
    [stepGlobal stepLocal event next event' nextLocal nextGlobal
      Hnb Htrace Hsem]; subst.
  rewrite Hsource in Htrace. inversion Htrace; subst.
  cbn in Hsem.
  destruct Hsem as (memory' & actualAddress & actualValue & Hsem).
  destruct Hsem as [Haddress Hsem].
  destruct Hsem as [Hvalue Hsem].
  destruct Hsem as [Hlen' Hbranch].
  apply writeSuccessBitsValInjective in Haddress. subst actualAddress.
  apply writeSuccessBitsValInjective in Hvalue. subst actualValue.
  rewrite Hread in Hbranch.
  destruct Hbranch as (-> & -> & -> & ->).
  repeat split; reflexivity.
Qed.

Lemma writeSuccessWriteMemMmioCovered local global labels afterLocal afterGlobal
    spawned trace' result kind (address : bv 64) len tag
    (value : bv (8 * len)) :
  local.(seq_trace) =
    WriteMem result kind (RVal_Bits (bv_to_bvn address))
      (RVal_Bits (bv_to_bvn value)) len tag Mk_annot :t: trace' ->
  (0 < Z.of_N len)%Z ->
  read_mem global.(seq_mem) (bv_unsigned address) len = None ->
  seq_step local global labels afterLocal afterGlobal spawned ->
  labels = [SWriteMem address (bv_to_bvn value)] /\
  afterLocal = local <| seq_trace := trace' |> /\
  afterGlobal = global /\
  spawned = [].
Proof.
  intros Hsource Hlen Hread Hstep.
  inversion Hstep as
    [stepGlobal stepLocal event next event' nextLocal nextGlobal
      Hnb Htrace Hsem]; subst.
  rewrite Hsource in Htrace. inversion Htrace; subst.
  cbn in Hsem.
  destruct Hsem as (memory' & actualAddress & actualValue & Hsem).
  destruct Hsem as [Haddress Hsem].
  destruct Hsem as [Hvalue Hsem].
  destruct Hsem as [Hlen' Hbranch].
  apply writeSuccessBitsValInjective in Haddress. subst actualAddress.
  apply writeSuccessBitsValInjective in Hvalue. subst actualValue.
  rewrite Hread in Hbranch.
  destruct Hbranch as (_ & _ & -> & -> & ->).
  repeat split; reflexivity.
Qed.

Print Assumptions writeSuccessInstructionPrefixAllNonblocking.
Print Assumptions writeSuccessBvToBvnInjective.
Print Assumptions writeSuccessBitsValInjective.
Print Assumptions writeSuccessInstructionSegmentPrefixAllNonblocking.
Print Assumptions writeSuccessDoneTabledCovered.
Print Assumptions writeSuccessDoneTrapCovered.
Print Assumptions writeSuccessReadRegCovered.
Print Assumptions writeSuccessAssumeCovered.
Print Assumptions writeSuccessDefineConstCovered.
Print Assumptions writeSuccessAssertCovered.
Print Assumptions writeSuccessAssumeRegCovered.
Print Assumptions writeSuccessWriteRegCovered.
Print Assumptions writeSuccessBranchAddressCovered.
Print Assumptions writeSuccessBranchCovered.
Print Assumptions writeSuccessReadMemBackedCovered.
Print Assumptions writeSuccessReadMemMmioCovered.
Print Assumptions writeSuccessWriteMemBackedCovered.
Print Assumptions writeSuccessWriteMemMmioCovered.
