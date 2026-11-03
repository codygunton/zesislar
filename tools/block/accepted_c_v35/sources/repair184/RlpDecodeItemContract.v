From Coq Require Import List ZArith.
Require Import EvmSailRlp.evm_rlp_types.
Require Import isla.riscv64.riscv64.
Require Import InstrSpecs.Machine.
Require Import ZesuSsz.Compliance.SailRun.
Require Import ZesuSsz.Compliance.KnownBugs.
Require Import ZesuSsz.Contracts.Level1.
Require Import ZesuSsz.Contracts.RlpDecodeItem.
Require Import ZesuSsz.Contracts.RlpDecodeItemSchema.
Import ListNotations.
Open Scope Z_scope.

(* The ABI assigns a0 to output, a1 to input, and a2 to input length.
   The caller owns the 40-byte result and the 16-byte stack frame. *)
Record DecodeItemArgs : Type := {
  decodeItemOutputPointer : Z;
  decodeItemInputPointer : Z;
  decodeItemInputLength : Z;
  decodeItemInputBytes : list byte;
  decodeItemBeforeStorage : list byte;
  decodeItemStackPointer : Z;
  decodeItemReturnAddress : Z;
  decodeItemSavedFramePointer : bv 64;
  decodeItemInputEnd : Z
}.

Definition DecodeItemOutcome : Type := list byte.

(* Only the input boundary has a decoder-specific exact value. *)
Definition decodeItemSysRegs (args : DecodeItemArgs) :
    list (reg_kind * valu_shape) :=
  map (fun '(r, shape) =>
    (r, if decide (r = KindReg "zisk_input_end")
        then ExactShape (RVal_Bits (Z_to_bv 64 (decodeItemInputEnd args)))
        else shape)) zesu_sys_regs.

Lemma decodeItemSysRegs_exact (args : DecodeItemArgs) :
  decodeItemSysRegs args = (machine_static_sys_regs defaultMap ++
    [(KindReg "zisk_input_end",
      ExactShape (RVal_Bits (Z_to_bv 64 (decodeItemInputEnd args))));
     (KindReg "zisk_free_input", BitsShape 64)])%list.
Proof. reflexivity. Qed.

Definition decodeItemArgsWellFormed (args : DecodeItemArgs) : Prop :=
  decodeItemInputLength args = Z.of_nat (List.length (decodeItemInputBytes args)) /\
  (List.length (decodeItemBeforeStorage args) = 40)%nat /\
  decodeItemEntryLayout
    (decodeItemInputPointer args) (decodeItemInputLength args)
    (decodeItemOutputPointer args) (decodeItemStackPointer args)
    (decodeItemReturnAddress args) (decodeItemInputEnd args).

Definition decodeItemC1BDomain (args : DecodeItemArgs) : Prop :=
  decodeItemArgsWellFormed args.

Definition decodeItemDomainAt (returnAddress : Z)
    (domain : DecodeItemArgs -> Prop) (args : DecodeItemArgs) : Prop :=
  decodeItemReturnAddress args = returnAddress /\ domain args.

Definition decodeItemAllows
    (R : Z -> list byte -> list byte -> list byte -> Prop)
    (args : DecodeItemArgs) (after : DecodeItemOutcome) : Prop :=
  R (decodeItemInputPointer args) (decodeItemInputBytes args)
    (decodeItemBeforeStorage args) after.

Definition decodeItemAllowsC1B : DecodeItemArgs -> DecodeItemOutcome -> Prop :=
  decodeItemAllows C1BResult.

Definition decodeItemSailCursor (args : DecodeItemArgs) :
    RlpCursor 0 (Z.of_nat (List.length (decodeItemInputBytes args))) :=
  {| StatelessInputSliceFields_bytes := 0;
     StatelessInputSliceFields_len :=
       Z.of_nat (List.length (decodeItemInputBytes args)) |}.

Definition decodeItemSailResult
    (args : DecodeItemArgs) (after : DecodeItemOutcome) : Prop :=
  @relateItem 0 (Z.of_nat (List.length (decodeItemInputBytes args)))
    (decodeItemInputPointer args)
    (decodeItemInputBytes args) (decodeItemBeforeStorage args) after
    (runRlpDecodeItem (decodeItemInputBytes args) (decodeItemSailCursor args)).

Definition decodeItemBugApplies (bug : KnownBug)
    (args : DecodeItemArgs) (after : DecodeItemOutcome) : Prop :=
  match bug with
  | RlpLongLengthWrap =>
      exists isList headerLength payloadLength,
        candidateDecodeItem (decodeItemInputBytes args) =
          candidateSuccess isList headerLength payloadLength /\
        binaryWrapCase headerLength payloadLength
          ((headerLength + payloadLength) mod word64Modulus) /\
        candidateResult40 (decodeItemInputPointer args)
          (decodeItemInputBytes args) (decodeItemBeforeStorage args) after /\
        runRlpDecodeItem (decodeItemInputBytes args)
          (decodeItemSailCursor args) = Reject RlpDecode
  end.

Definition DecodeMeaningModuloKnownBugs
    (args : DecodeItemArgs) (after : DecodeItemOutcome) : Prop :=
  decodeItemAllowsC1B args after /\
  (decodeItemSailResult args after \/
   exists bug, List.In bug knownBugs /\ decodeItemBugApplies bug args after).

Definition decodeItemWrapWitnessInput : list byte :=
  List.map (Z_to_bv 8) [191; 255; 255; 255; 255; 255; 255; 255; 247].

Lemma decodeItemWrapWitness :
  candidateDecodeItem decodeItemWrapWitnessInput =
    candidateSuccess false 9 (word64Modulus - 9) /\
  binaryWrapCase 9 (word64Modulus - 9) 0 /\
  ~ headerFits decodeItemWrapWitnessInput.
Proof.
  vm_compute; repeat split; try congruence.
  intros [H | [H | H]]; discriminate.
Qed.

Definition decodeItemEntryResources `{!islaG Sigma} `{!threadG}
    (domain : DecodeItemArgs -> Prop) (args : DecodeItemArgs) : iProp Sigma :=
  (∃ (a3 a4 a5 a6 : bv 64),
   reg_col (decodeItemSysRegs args) ∗
   "x10" ↦ᵣ RVal_Bits (Z_to_bv 64 (decodeItemOutputPointer args)) ∗
   "x11" ↦ᵣ RVal_Bits (Z_to_bv 64 (decodeItemInputPointer args)) ∗
   "x12" ↦ᵣ RVal_Bits (Z_to_bv 64 (decodeItemInputLength args)) ∗
   "x13" ↦ᵣ RVal_Bits a3 ∗
   "x14" ↦ᵣ RVal_Bits a4 ∗
   "x15" ↦ᵣ RVal_Bits a5 ∗
   "x16" ↦ᵣ RVal_Bits a6 ∗
   "x2" ↦ᵣ RVal_Bits (Z_to_bv 64 (decodeItemStackPointer args)) ∗
   "x1" ↦ᵣ RVal_Bits (Z_to_bv 64 (decodeItemReturnAddress args)) ∗
   "x8" ↦ᵣ RVal_Bits (decodeItemSavedFramePointer args) ∗
   decodeItemInputPointer args ↦ₘ∗ decodeItemInputBytes args ∗
   decodeItemOutputPointer args ↦ₘ∗ decodeItemBeforeStorage args ∗
   (decodeItemStackPointer args - decodeItemStackBytes) ↦ₘ? decodeItemStackBytes ∗
   ⌜domain args⌝ ∗ True)%I.

Definition decodeItemExitResources `{!islaG Sigma} `{!threadG}
    (args : DecodeItemArgs) (after : DecodeItemOutcome) : iProp Sigma :=
  (reg_col (decodeItemSysRegs args) ∗
   "x2" ↦ᵣ RVal_Bits (Z_to_bv 64 (decodeItemStackPointer args)) ∗
   "x1" ↦ᵣ RVal_Bits (Z_to_bv 64 (decodeItemReturnAddress args)) ∗
   "x8" ↦ᵣ RVal_Bits (decodeItemSavedFramePointer args) ∗
   decodeItemInputPointer args ↦ₘ∗ decodeItemInputBytes args ∗
   decodeItemOutputPointer args ↦ₘ∗ after ∗
   (decodeItemStackPointer args - decodeItemStackBytes) ↦ₘ? decodeItemStackBytes ∗
   True)%I.

Definition decodeItemResources `{!islaG Sigma} `{!threadG}
    (code : iProp Sigma) (domain : DecodeItemArgs -> Prop) :
    IslarisContractResources DecodeItemArgs DecodeItemOutcome :=
  {| islarisCode := code;
     islarisEntry := decodeItemEntryResources domain;
     islarisExit := decodeItemExitResources |}.
