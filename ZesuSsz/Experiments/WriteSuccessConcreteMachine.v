From Coq Require Import Lists.List ZArith.ZArith.
Require Import isla.opsem.
Require Import isla.ghost_state.
Require Import isla.lifting.
From IslaTraces.write_success_00 Require Import a14d30.
Require Import ZesuSsz.Contracts.Level1.
Require Import ZesuSsz.Contracts.IslarisMachine.
Require Import ZesuSsz.Contracts.InstructionBoundary.
Require Import ZesuSsz.Generated.WriteSuccessCertificate.
Require Import ZesuSsz.Experiments.WriteSuccessObservation.
Require Import ZesuSsz.Experiments.WriteSuccessConcreteRepresentation.
Require Import ZesuSsz.Experiments.WriteSuccessConcreteRepresentationOff.
Require Import ZesuSsz.Experiments.WriteSuccessConcreteRepresentationOffLegacy.
Require Import ZesuSsz.Experiments.WriteSuccessObservationDecoder.
Require Import ZesuSsz.Experiments.WriteSuccessPrologueSpec.
Require Import ZesuSsz.Experiments.WriteSuccessNativeContract.
Require Import ZesuSsz.Experiments.WriteSuccessHostObservation.

Open Scope Z_scope.

Definition WriteSuccessConcreteState : Type :=
  (seq_local_state * seq_global_state)%type.

Definition writeSuccessConcretePc
    (state : WriteSuccessConcreteState) : option Z :=
  match state.1.(seq_regs) !! state.1.(seq_pc_reg) with
  | Some (RVal_Bits value) => Some (bvn_unsigned value)
  | _ => None
  end.

Definition writeSuccessConcreteStep (_ : nat)
    (before after : WriteSuccessConcreteState) : Prop :=
  exists observations, IslaInstructionSegment before observations after.

Definition writeSuccessConcreteDecodedPointer
    (state : WriteSuccessConcreteState) : option Z :=
  match state.1.(seq_regs) !! "x10" with
  | Some (RVal_Bits value) => Some (bvn_unsigned value)
  | _ => None
  end.

Definition writeSuccessConcreteRegister64
    (registers : reg_map) (name : string) : Prop :=
  exists value : bv 64, registers !! name = Some (RVal_Bits value).

Definition writeSuccessConcreteAbiRegisters : list string :=
  ["x1"; "x2"; "x8"; "x9"; "x10"; "x11"; "x12";
   "x18"; "x19"; "x20"; "x21"; "x22"; "x23"; "x24";
   "x25"; "x26"; "x27"] ++ writeSuccessOtherRegisters.

Definition writeSuccessConcreteInitialState
    (args : WriteSuccessArgs WriteSuccessObservation)
    (state : WriteSuccessConcreteState) : Prop :=
  state.1.(seq_trace) = a14d30 /\
  state.1.(seq_pc_reg) = "PC" /\
  state.1.(seq_nb_state) = false /\
  state.2.(seq_instrs) !! Z_to_bv 64 0x14d30 = Some a14d30 /\
  (forall fromPc toPc,
    In (fromPc, toPc) writeSuccessGeneratedControlFlow ->
    exists trace,
      state.2.(seq_instrs) !! Z_to_bv 64 fromPc = Some trace) /\
  state.1.(seq_regs) !! "PC" = Some (RVal_Bits (Z_to_bv 64 0x14d30)) /\
  state.1.(seq_regs) !! "x1" = Some
    (RVal_Bits (Z_to_bv 64 (successReturnAddress WriteSuccessObservation args))) /\
  state.1.(seq_regs) !! "x2" = Some
    (RVal_Bits (Z_to_bv 64 (successStackPointer WriteSuccessObservation args))) /\
  state.1.(seq_regs) !! "x10" = Some
    (RVal_Bits (Z_to_bv 64 (successDecodedAddress WriteSuccessObservation args))) /\
  Forall (writeSuccessConcreteRegister64 state.1.(seq_regs))
    writeSuccessConcreteAbiRegisters /\
  Forall (fun item =>
      match item.1 with
      | KindReg name => exists value,
          state.1.(seq_regs) !! name = Some value /\
          valu_has_shape value item.2
      | KindField _ _ => False
      end) zesu_ram_sys_regs /\
  successReturnAddress WriteSuccessObservation args = 0x14d10 /\
  successStackPointer WriteSuccessObservation args `mod` 16 = 0 /\
  (0x20000880 <= successStackPointer WriteSuccessObservation args)%Z /\
  (successStackPointer WriteSuccessObservation args + 0x7d0 < 0x40000000)%Z /\
  (exists stackBytes,
    length stackBytes = 1896%nat /\
    read_mem_list state.2.(seq_mem)
      (successStackPointer WriteSuccessObservation args - 0x7d0) 1896%N =
      Some stackBytes) /\
  set_Forall (fun address =>
    ~ (0x2401a0c0 <= bv_unsigned address < 0x2401a0d0)%Z)
    (dom state.2.(seq_mem)).

Definition writeSuccessConcreteEntry
    (args : WriteSuccessArgs WriteSuccessObservation)
    (state : WriteSuccessConcreteState) : Prop :=
  writeSuccessConcretePc state = Some 0x14d30 /\
  writeSuccessConcreteInitialState args state /\
  writeSuccessConcreteDecodedPointer state =
    Some (successDecodedAddress WriteSuccessObservation args) /\
  writeSuccessConcreteRepresentationOff
    (successStackPointer WriteSuccessObservation args)
    (successDecoded WriteSuccessObservation args) state.2.(seq_mem)
    (successDecodedAddress WriteSuccessObservation args).

Definition writeSuccessConcreteEntryRepresentation
    (decoded : WriteSuccessObservation)
    (state : WriteSuccessConcreteState) : Prop :=
  exists address,
    writeSuccessConcreteDecodedPointer state = Some address /\
    writeSuccessConcreteRepresentation decoded state.2.(seq_mem) address.

Definition writeSuccessConcreteBytesRepresentation
    (decoded : WriteSuccessObservation) (bytes : list (bv 8)) : Prop :=
  exists memory address,
    writeSuccessConcreteRepresentation decoded memory address /\
    read_mem_list memory address 848%N = Some bytes.

Lemma writeSuccessConcreteEntryRepresentationLaw args state :
  writeSuccessConcreteEntry args state ->
  writeSuccessConcreteEntryRepresentation
    (successDecoded WriteSuccessObservation args) state.
Proof.
  intros (_ & _ & Hpointer & Hrepresentation).
  exists (successDecodedAddress WriteSuccessObservation args). auto.
Qed.

Lemma writeSuccessConcreteEntryInstructionBoundary args state :
  writeSuccessConcreteEntry args state ->
  IslaInstructionBoundary state.
Proof.
  intros (_ & Hinitial & _).
  unfold writeSuccessConcreteInitialState in Hinitial.
  destruct Hinitial as
    (Htrace & HpcReg & Hnonblocking & Hinstruction & Htable & Hpc & _).
  split; first exact Hnonblocking.
  exists (Z_to_bv 64 0x14d30), a14d30.
  rewrite HpcReg in Hpc |- *.
  split; first exact Hpc. split; assumption.
Qed.

Lemma writeSuccessConcreteEntryNativeRepresentation args state witness :
  writeSuccessConcreteEntry args state ->
  writeSuccessWitnessWellFormed args witness ->
  read_mem_list state.2.(seq_mem)
    (bv_unsigned (writeSuccessDecodedPointer witness)) 848%N =
    Some (writeSuccessDecodedBytes witness) ->
  writeSuccessConcreteBytesRepresentation
    (successDecoded WriteSuccessObservation args)
    (writeSuccessDecodedBytes witness).
Proof.
  intros (_ & _ & Hpointer & Hrepresentation) Hwell Hread.
  unfold writeSuccessWitnessWellFormed in Hwell.
  destruct Hwell as (_ & Haddress & _).
  exists state.2.(seq_mem),
    (successDecodedAddress WriteSuccessObservation args).
  split; first exact (writeSuccessConcreteRepresentationOffLegacy
    _ _ _ _ Hrepresentation).
  rewrite Haddress. exact Hread.
Qed.

(** The authoritative machine memory and the owned entry bytes describe the
    same concrete bytes.  This is the ownership-to-representation law used at
    the caller boundary. *)
Lemma writeSuccessConcreteOwnedEntryRepresentation
    `{!islaG Sigma} `{!threadG}
    (args : WriteSuccessArgs WriteSuccessObservation)
    (state : WriteSuccessConcreteState)
    (witness : writeSuccessNativeWitness WriteSuccessObservation) :
  writeSuccessConcreteEntry args state ->
  writeSuccessWitnessWellFormed args witness ->
  state_ctx state.2 [] ∗
    bv_unsigned (writeSuccessDecodedPointer witness) ↦ₘ∗
      writeSuccessDecodedBytes witness -∗
  ⌜writeSuccessConcreteBytesRepresentation
      (successDecoded WriteSuccessObservation args)
      (writeSuccessDecodedBytes witness)⌝ ∗
  state_ctx state.2 [] ∗
    bv_unsigned (writeSuccessDecodedPointer witness) ↦ₘ∗
      writeSuccessDecodedBytes witness.
Proof.
  iIntros (Hentry Hwell) "[Hstate Hbytes]".
  iAssert ⌜read_mem_list state.2.(seq_mem)
      (bv_unsigned (writeSuccessDecodedPointer witness))
      (N.of_nat (length (writeSuccessDecodedBytes witness))) =
        Some (writeSuccessDecodedBytes witness)⌝%I as %Hread.
  { iApply (writeSuccessOwnedPayloadRead with "Hstate Hbytes"). }
  pose proof Hwell as HwellCopy.
  unfold writeSuccessWitnessWellFormed in HwellCopy.
  destruct HwellCopy as
    (_ & _ & _ & _ & _ & HdecodedLength & _).
  rewrite HdecodedLength in Hread.
  change (N.of_nat 848) with 848%N in Hread.
  iSplitR "Hstate Hbytes".
  - iPureIntro.
    eapply writeSuccessConcreteEntryNativeRepresentation; eassumption.
  - iFrame.
Qed.

Lemma writeSuccessConcreteOwnedEntryFieldExamples
    `{!islaG Sigma} `{!threadG}
    (args : WriteSuccessArgs WriteSuccessObservation)
    (state : WriteSuccessConcreteState)
    (witness : writeSuccessNativeWitness WriteSuccessObservation) :
  writeSuccessConcreteEntry args state ->
  writeSuccessWitnessWellFormed args witness ->
  state_ctx state.2 [] ∗
    bv_unsigned (writeSuccessDecodedPointer witness) ↦ₘ∗
      writeSuccessDecodedBytes witness -∗
  ⌜exists address,
      writeSuccessConcreteDecodedPointer state = Some address /\
      writeSuccessConcreteRepresentation
        (successDecoded WriteSuccessObservation args) state.2.(seq_mem)
        address /\
      read_mem_list state.2.(seq_mem) address 848%N =
        Some (writeSuccessDecodedBytes witness) /\
      writeSuccessMemoryInteger state.2.(seq_mem) (address + 48) 8
        (observationBaseFee
          (successDecoded WriteSuccessObservation args)) /\
      writeSuccessMemorySlice state.2.(seq_mem) address 32
        (observationExtraData
          (successDecoded WriteSuccessObservation args))⌝ ∗
  state_ctx state.2 [] ∗
    bv_unsigned (writeSuccessDecodedPointer witness) ↦ₘ∗
      writeSuccessDecodedBytes witness.
Proof.
  iIntros (Hentry Hwell) "[Hstate Hbytes]".
  iAssert ⌜read_mem_list state.2.(seq_mem)
      (bv_unsigned (writeSuccessDecodedPointer witness))
      (N.of_nat (length (writeSuccessDecodedBytes witness))) =
        Some (writeSuccessDecodedBytes witness)⌝%I as %Hread.
  { iApply (writeSuccessOwnedPayloadRead with "Hstate Hbytes"). }
  pose proof Hwell as HwellCopy.
  unfold writeSuccessWitnessWellFormed in HwellCopy.
  destruct HwellCopy as
    (_ & Haddress & _ & _ & _ & HdecodedLength & _).
  rewrite HdecodedLength in Hread.
  change (N.of_nat 848) with 848%N in Hread.
  destruct Hentry as (_ & _ & Hpointer & Hrepresentation).
  have Hread' : read_mem_list state.2.(seq_mem)
      (successDecodedAddress WriteSuccessObservation args) 848%N =
        Some (writeSuccessDecodedBytes witness).
  { rewrite Haddress. exact Hread. }
  iSplitR "Hstate Hbytes".
  - iPureIntro.
    pose proof (writeSuccessRepresentationBaseFee _ _ _ Hrepresentation)
      as HbaseFee.
    pose proof (writeSuccessRepresentationExtraData _ _ _ Hrepresentation)
      as HextraData.
    exists (successDecodedAddress WriteSuccessObservation args).
    exact (conj Hpointer (conj Hrepresentation
      (conj Hread' (conj HbaseFee HextraData)))).
  - iFrame "Hstate Hbytes".
Qed.

Lemma writeSuccessNativeEntryDecodedBytesAccess
    `{!islaG Sigma} `{!threadG}
    (args : WriteSuccessArgs WriteSuccessObservation) :
  writeSuccessNativeEntry args -∗
  ∃ witness : writeSuccessNativeWitness WriteSuccessObservation,
    ⌜writeSuccessWitnessWellFormed args witness⌝ ∗
    bv_unsigned (writeSuccessDecodedPointer witness) ↦ₘ∗
      writeSuccessDecodedBytes witness ∗
    (bv_unsigned (writeSuccessDecodedPointer witness) ↦ₘ∗
       writeSuccessDecodedBytes witness -∗
     write_success_prologue_entry
       (writeSuccessEntrySp witness) (writeSuccessDecodedPointer witness)
       (writeSuccessReturnValue witness)
       (writeSuccessSavedS0 witness) (writeSuccessSavedS1 witness)
       (writeSuccessSavedS2 witness) (writeSuccessSavedS3 witness)
       (writeSuccessSavedS4 witness) (writeSuccessSavedS5 witness)
       (writeSuccessSavedS6 witness) (writeSuccessSavedS7 witness)
       (writeSuccessSavedS8 witness) (writeSuccessSavedS9 witness)
       (writeSuccessSavedS10 witness) (writeSuccessSavedS11 witness)
       (writeSuccessProloguePayload witness)).
Proof.
  rewrite /writeSuccessNativeEntry.
  iDestruct 1 as (witness Hwell) "Hentry".
  rewrite /write_success_prologue_entry.
  iDestruct "Hentry" as
    "(Hsys & Hother & Hx1 & Hx2 & Hx8 & Hx9 & Hx18 & Hx19 & Hx20 &
      Hx21 & Hx22 & Hx23 & Hx24 & Hx25 & Hx26 & Hx27 & Hx10 & Hx11)".
  rewrite reg_mapsto_pred_eq /reg_mapsto_pred_def.
  iDestruct "Hx11" as (v11) "[Hx11 Hx12]".
  iDestruct "Hx12" as (v12) "[Hx12 [Hscratch Hfacts]]".
  rewrite /writeSuccessPrologueFacts.
  iDestruct "Hfacts" as
    "(%Hdecoded & %Halign & %Hmin & %Hmax & Hpayload & _)".
  rewrite /writeSuccessProloguePayload.
  iDestruct "Hpayload" as
    "(Huninit & Hbytes & Hmmio & Hspec & Hdata & %Hlength &
      %HpointerMin & %HpointerMax & _)".
  iExists witness. iFrame "%".
  iSplitL "Hbytes"; first iExact "Hbytes".
  iIntros "Hbytes".
  rewrite /write_success_prologue_entry.
  iFrame "Hsys Hother Hx1 Hx2 Hx8 Hx9 Hx18 Hx19 Hx20 Hx21 Hx22
    Hx23 Hx24 Hx25 Hx26 Hx27 Hx10".
  iExists v11. iFrame "Hx11".
  iExists v12. iFrame "Hx12 Hscratch".
  rewrite /writeSuccessPrologueFacts /writeSuccessProloguePayload.
  iFrame "Hbytes Huninit Hmmio Hspec Hdata".
Qed.

Definition writeSuccessConcreteModel :
    Level1MachineModel WriteSuccessConcreteState WriteSuccessObservation.
Proof.
  refine {|
    endpointStep := writeSuccessConcreteStep;
    endpointPc := writeSuccessConcretePc;
    readInputEntry := fun _ _ => False;
    readInputExit := fun _ _ _ _ => False;
    allocatorGetEntry := fun _ _ => False;
    allocatorGetExit := fun _ _ _ _ => False;
    decodeBoundaryEntry := fun _ _ => False;
    decodeBoundaryExit := fun _ _ _ _ => False;
    writeSuccessEntry := writeSuccessConcreteEntry;
    writeSuccessEntryRepresentation := writeSuccessConcreteEntryRepresentation;
    writeSuccessEntryRepresents := writeSuccessConcreteEntryRepresentationLaw;
    writeSuccessExit := fun args bytes _ after =>
      writeSuccessConcretePc after = Some 0x14d10 /\
      writeSuccessDecodeObservation bytes =
        Some (successDecoded WriteSuccessObservation args);
    writeFailureEntry := fun _ _ => False;
    writeFailureExit := fun _ _ _ _ => False;
    zkvmExitEntry := fun _ _ => False;
    zkvmExitPost := fun _ _ _ _ => False;
    referenceDecodes := fun bytes decoded =>
      writeSuccessDecodeObservation bytes = Some decoded;
    decodedResultRelModuloKnownBugs := fun bytes _ decoded =>
      writeSuccessDecodeObservation bytes = Some decoded;
    avoidsReviewedDomainDivergences := fun _ _ => True;
    knownBugApplies := fun _ _ _ => False;
    decodeObservationSuccess := fun bytes decoded =>
      writeSuccessDecodeObservation bytes = Some decoded;
    decodeObservationFailure := fun bytes =>
      writeSuccessDecodeObservation bytes = None
  |}.
Defined.

Lemma writeSuccessConcreteModelRepresentation args state :
  ZesuSsz.Contracts.Level1.writeSuccessEntry
      WriteSuccessConcreteState WriteSuccessObservation
      writeSuccessConcreteModel args state ->
  writeSuccessEntryRepresentation
      WriteSuccessConcreteState WriteSuccessObservation
      writeSuccessConcreteModel
      (successDecoded WriteSuccessObservation args) state.
Proof.
  exact (writeSuccessEntryRepresents _ _ writeSuccessConcreteModel args state).
Qed.

Definition writeSuccessConcreteEntryResources
    `{!islaG Sigma} `{!threadG}
    (args : WriteSuccessArgs WriteSuccessObservation)
    (state : WriteSuccessConcreteState) : iProp Sigma :=
  (state_ctx state.2 [] ∗ thread_ctx state.1.(seq_regs) ∗
   writeSuccessNativeEntry args ∗
   ⌜writeSuccessConcreteEntry args state⌝)%I.

Lemma writeSuccessConcreteEntryResourcesReflect
    `{!islaG Sigma} `{!threadG}
    (args : WriteSuccessArgs WriteSuccessObservation)
    (state : WriteSuccessConcreteState) :
  writeSuccessConcreteEntryResources args state -∗
  writeSuccessConcreteEntryResources args state ∗
  ⌜writeSuccessConcreteEntryRepresentation
    (successDecoded WriteSuccessObservation args) state⌝.
Proof.
  iIntros "Hentry".
  iDestruct "Hentry" as "(Hstate & Hthread & Hnative & %Hrelation)".
  iFrame. iSplit.
  - iPureIntro. exact Hrelation.
  - iPureIntro. apply writeSuccessConcreteEntryRepresentationLaw.
    exact Hrelation.
Qed.

Lemma writeSuccessConcreteEntryBlockingStateRejected args state :
  state.1.(seq_nb_state) = true ->
  ~ writeSuccessConcreteEntry args state.
Proof.
  intros Hblocking (_ & Hinitial & _).
  unfold writeSuccessConcreteInitialState in Hinitial.
  destruct Hinitial as (_ & _ & Hnonblocking & _).
  congruence.
Qed.

Print Assumptions writeSuccessConcreteEntryInstructionBoundary.
Print Assumptions writeSuccessConcreteEntryBlockingStateRejected.
Print Assumptions writeSuccessConcreteOwnedEntryRepresentation.
Print Assumptions writeSuccessConcreteOwnedEntryFieldExamples.
Print Assumptions writeSuccessNativeEntryDecodedBytesAccess.
