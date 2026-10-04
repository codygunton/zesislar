From Coq Require Import List ZArith.
Require Import isla.opsem.
Require Import ZesuSsz.Contracts.RlpDecodeItem.
Require Import ZesuSsz.Contracts.RlpDecodeItemContract.
Require Import ZesuSsz.Contracts.RlpDecodeItemByteFold.
Require Import ZesuSsz.Export.Executor.
Require Import ZesuSsz.Export.TerminationResources.
Import ListNotations.
Open Scope Z_scope.

(* These definitions state Phase 5 obligations. They do not prove completion.
   CompletedInstructionRun is relational; Executor has no multi-instruction
   executable driver. Both bounds must be proved for a completed run. *)
Definition decodeItemBoundedRun (instructionLimit stepLimit : nat)
    (start finish : seq_local_state) (before after : seq_global_state) : Prop :=
  exists instructions steps labels,
    (instructions <= instructionLimit)%nat /\
    (steps <= stepLimit)%nat /\
    CompletedInstructionRun instructions start before labels finish after /\
    @nsteps isla_lang steps ([start], before) labels ([finish], after).

(* At either long-length header, n is the number of length bytes and i is
   the number already folded. The measure decreases on every byte step. *)
Definition decodeItemByteFoldMeasure (n i : Z) : nat := Z.to_nat (n - i).

Definition decodeItemByteFoldStep (args : DecodeItemArgs) (isList : bool)
    (n i payloadStart : Z) (lengthBytes : list byte)
    (start finish : seq_local_state) (before after : seq_global_state) : Prop :=
  decodeItemByteFoldFacts args n i payloadStart lengthBytes /\ i < n /\
  physicalRegister64 (seq_regs start) "PC"
    (Z_to_bv 64 (decodeItemByteFoldHeader isList)) /\
  physicalRegister64 (seq_regs start) "x15" (Z_to_bv 64 (payloadStart + i)) /\
  physicalRegister64 (seq_regs finish) "x15"
    (Z_to_bv 64 (payloadStart + i + 1)) /\
  decodeItemByteFoldMeasure n (i + 1) < decodeItemByteFoldMeasure n i /\
  exists instructions steps labels,
    (0 < instructions)%nat /\ (0 < steps)%nat /\
    CompletedInstructionRun instructions start before labels finish after /\
    @nsteps isla_lang steps ([start], before) labels ([finish], after).

Definition decodeItemStringByteFoldStep (args : DecodeItemArgs)
    (n i payloadStart : Z) (lengthBytes : list byte)
    (start finish : seq_local_state) (before after : seq_global_state) : Prop :=
  decodeItemByteFoldStep args false n i payloadStart lengthBytes
    start finish before after.

Definition decodeItemListByteFoldStep (args : DecodeItemArgs)
    (n i payloadStart : Z) (lengthBytes : list byte)
    (start finish : seq_local_state) (before after : seq_global_state) : Prop :=
  decodeItemByteFoldStep args true n i payloadStart lengthBytes
    start finish before after.

Definition decodeItemByteFoldBound (args : DecodeItemArgs) (isList : bool)
    (n i payloadStart : Z) (lengthBytes : list byte)
    (start : seq_local_state) : Prop :=
  decodeItemByteFoldFacts args n i payloadStart lengthBytes /\
  physicalRegister64 (seq_regs start) "PC"
    (Z_to_bv 64 (decodeItemByteFoldHeader isList)) /\
  (decodeItemByteFoldMeasure n i <= 8)%nat /\
  forall j, i <= j < n ->
    decodeItemByteFoldMeasure n (j + 1) < decodeItemByteFoldMeasure n j.

Definition decodeItemStringByteFoldBound (args : DecodeItemArgs)
    (n i payloadStart : Z) (lengthBytes : list byte)
    (start : seq_local_state) : Prop :=
  decodeItemByteFoldBound args false n i payloadStart lengthBytes start.

Definition decodeItemListByteFoldBound (args : DecodeItemArgs)
    (n i payloadStart : Z) (lengthBytes : list byte)
    (start : seq_local_state) : Prop :=
  decodeItemByteFoldBound args true n i payloadStart lengthBytes start.

(* Every edge in the path consumes one byte. The path length fixes the
   iteration count; the step relation supplies completed instructions. *)
Definition decodeItemByteFoldPath (args : DecodeItemArgs) (isList : bool)
    (n i payloadStart : Z) (lengthBytes : list byte)
    (states : list (seq_local_state * seq_global_state)) : Prop :=
  length states = S (decodeItemByteFoldMeasure n i) /\
  forall k, (k < decodeItemByteFoldMeasure n i)%nat ->
    exists start before finish after,
      nth_error states k = Some (start, before) /\
      nth_error states (S k) = Some (finish, after) /\
      decodeItemByteFoldStep args isList n (i + Z.of_nat k)
        payloadStart lengthBytes start finish before after.

Definition decodeItemByteFoldCompletion (args : DecodeItemArgs) (isList : bool)
    (n i payloadStart : Z) (lengthBytes : list byte)
    (instructionLimit stepLimit : nat)
    (start finish : seq_local_state) (before after : seq_global_state) : Prop :=
  decodeItemByteFoldBound args isList n i payloadStart lengthBytes start /\
  exists states,
    decodeItemByteFoldPath args isList n i payloadStart lengthBytes states /\
    hd_error states = Some (start, before) /\
    last states = Some (finish, after) /\
    physicalRegister64 (seq_regs finish) "x15"
      (Z_to_bv 64 (payloadStart + n)) /\
    decodeItemBoundedRun instructionLimit stepLimit start finish before after.

Definition decodeItemStringByteFoldCompletion (args : DecodeItemArgs)
    (n i payloadStart : Z) (lengthBytes : list byte)
    (instructionLimit stepLimit : nat)
    (start finish : seq_local_state) (before after : seq_global_state) : Prop :=
  decodeItemByteFoldCompletion args false n i payloadStart lengthBytes
    instructionLimit stepLimit start finish before after.

Definition decodeItemListByteFoldCompletion (args : DecodeItemArgs)
    (n i payloadStart : Z) (lengthBytes : list byte)
    (instructionLimit stepLimit : nat)
    (start finish : seq_local_state) (before after : seq_global_state) : Prop :=
  decodeItemByteFoldCompletion args true n i payloadStart lengthBytes
    instructionLimit stepLimit start finish before after.

(* This binding still needs a proof that the fetched trace is the selected
   ELF instruction at decodeItemEntry. It does not provide that index. *)
Definition decodeItemEntryTraceBound (start : seq_local_state)
    (before : seq_global_state) : Prop :=
  seq_pc_reg start = "PC" /\
  seq_trace start <> tnil /\
  seq_instrs before !! Z_to_bv 64 decodeItemEntry = Some (seq_trace start).

Definition decodeItemPhysicalEntry (args : DecodeItemArgs)
    (start : seq_local_state) (before : seq_global_state) : Prop :=
  decodeItemC1BDomain args /\
  seq_nb_state start = false /\
  decodeItemEntryTraceBound start before /\
  physicalRegister64 (seq_regs start) "PC" (Z_to_bv 64 decodeItemEntry) /\
  physicalRegister64 (seq_regs start) "x10"
    (Z_to_bv 64 (decodeItemOutputPointer args)) /\
  physicalRegister64 (seq_regs start) "x11"
    (Z_to_bv 64 (decodeItemInputPointer args)) /\
  physicalRegister64 (seq_regs start) "x12"
    (Z_to_bv 64 (decodeItemInputLength args)) /\
  physicalRegister64 (seq_regs start) "x2"
    (Z_to_bv 64 (decodeItemStackPointer args)) /\
  physicalRegister64 (seq_regs start) "x1"
    (Z_to_bv 64 (decodeItemReturnAddress args)) /\
  physicalRegister64 (seq_regs start) "x8"
    (decodeItemSavedFramePointer args) /\
  physicalMemoryBytes before (decodeItemInputPointer args)
    (decodeItemInputBytes args) /\
  physicalMemoryBytes before (decodeItemOutputPointer args)
    (decodeItemBeforeStorage args).

Definition decodeItemPhysicalReturn (args : DecodeItemArgs)
    (result : DecodeItemOutcome) (finish : seq_local_state)
    (after : seq_global_state) : Prop :=
  seq_nb_state finish = false /\
  physicalRegister64 (seq_regs finish) "PC"
    (Z_to_bv 64 (decodeItemReturnAddress args)) /\
  physicalRegister64 (seq_regs finish) "x2"
    (Z_to_bv 64 (decodeItemStackPointer args)) /\
  physicalRegister64 (seq_regs finish) "x1"
    (Z_to_bv 64 (decodeItemReturnAddress args)) /\
  physicalRegister64 (seq_regs finish) "x8"
    (decodeItemSavedFramePointer args) /\
  physicalMemoryBytes after (decodeItemInputPointer args)
    (decodeItemInputBytes args) /\
  physicalMemoryBytes after (decodeItemOutputPointer args) result /\
  decodeItemAllowsC1B args result.

(* This internal candidate states the intended bound. The selected-ELF
   trace binding, machine conditions, and block summaries remain open. *)
Definition decodeItemC1BTerminationCandidate
    (instructionLimit stepLimit : DecodeItemArgs -> nat) : Prop :=
  forall args start before,
    decodeItemPhysicalEntry args start before ->
    exists finish after result,
      decodeItemBoundedRun (instructionLimit args) (stepLimit args)
        start finish before after /\
      decodeItemPhysicalReturn args result finish after.
