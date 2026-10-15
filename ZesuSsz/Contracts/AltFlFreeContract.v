From Coq Require Import List ZArith.
Require Import isla.riscv64.riscv64.
Require Import EvmSailRlp.evm_rlp_types.
Require Import InstrSpecs.Machine.
Require Import ZesuSsz.Contracts.Level1.
Require Import ZesuSsz.Contracts.AltFlFree.
Open Scope Z_scope.

Record FreeArgs : Type := {
  freeBufferPointer : Z;
  freeBufferLength : Z;
  freeLog2Alignment : Z;
  freeBeforeBuffer : list byte;
  freeBeforeLists : list byte;
  freeStackPointer : Z;
  freeReturnAddress : Z;
  freeSavedFramePointer : bv 64
}.

Record FreeOutcome : Type := {
  freeAfterBuffer : list byte;
  freeAfterLists : list byte
}.

Definition freeRange (pointer length : Z) : Prop :=
  0xa0000000 <= pointer /\ 0 <= length /\ pointer + length <= 0xc0000000.
Definition freeSeparate (p n q m : Z) : Prop :=
  p + n <= q \/ q + m <= p.

Definition freeArgsWellFormed (args : FreeArgs) : Prop :=
  0 <= freeBufferLength args < 2 ^ 64 /\
  0 <= freeLog2Alignment args < 64 /\
  8 <= Z.of_nat (length (freeBeforeBuffer args)) /\
  freeBufferLength args <= Z.of_nat (length (freeBeforeBuffer args)) /\
  length (freeBeforeLists args) = 184%nat /\
  freeRange (freeBufferPointer args) (Z.of_nat (length (freeBeforeBuffer args))) /\
  freeRange freeListsPointer freeListsBytes /\
  freeRange (freeStackPointer args - freeStackBytes) freeStackBytes /\
  freeStackPointer args mod 16 = 0 /\
  0 <= freeReturnAddress args < 2 ^ 64 /\ freeReturnAddress args mod 4 = 0 /\
  freeSeparate (freeBufferPointer args) (Z.of_nat (length (freeBeforeBuffer args)))
    freeListsPointer freeListsBytes /\
  freeSeparate (freeBufferPointer args) (Z.of_nat (length (freeBeforeBuffer args)))
    (freeStackPointer args - freeStackBytes) freeStackBytes /\
  freeSeparate freeListsPointer freeListsBytes
    (freeStackPointer args - freeStackBytes) freeStackBytes.

Definition freeAllows (args : FreeArgs) (after : FreeOutcome) : Prop :=
  freeResultImages (freeBufferPointer args) (freeBufferLength args)
    (freeLog2Alignment args) (freeBeforeBuffer args) (freeBeforeLists args)
    (freeAfterBuffer after) (freeAfterLists after).

Definition freeEntryResources `{!islaG Sigma} `{!threadG}
    (args : FreeArgs) : iProp Sigma :=
  (∃ (x10 x14 : bv 64),
   reg_col zesu_sys_regs ∗
   "x1" ↦ᵣ RVal_Bits (Z_to_bv 64 (freeReturnAddress args)) ∗
   "x2" ↦ᵣ RVal_Bits (Z_to_bv 64 (freeStackPointer args)) ∗
   "x8" ↦ᵣ RVal_Bits (freeSavedFramePointer args) ∗
   "x10" ↦ᵣ RVal_Bits x10 ∗
   "x11" ↦ᵣ RVal_Bits (Z_to_bv 64 (freeBufferPointer args)) ∗
   "x12" ↦ᵣ RVal_Bits (Z_to_bv 64 (freeBufferLength args)) ∗
   "x13" ↦ᵣ RVal_Bits (Z_to_bv 64 (freeLog2Alignment args)) ∗
   "x14" ↦ᵣ RVal_Bits x14 ∗
   freeBufferPointer args ↦ₘ∗ freeBeforeBuffer args ∗
   freeListsPointer ↦ₘ∗ freeBeforeLists args ∗
   (freeStackPointer args - freeStackBytes) ↦ₘ? freeStackBytes ∗
   ⌜freeArgsWellFormed args⌝ ∗ True)%I.

Definition freeExitRegisterResources `{!islaG Sigma} `{!threadG}
    (args : FreeArgs) : iProp Sigma :=
  (∃ (x10 x12 x13 x14 : bv 64),
   reg_col zesu_sys_regs ∗
   "x1" ↦ᵣ RVal_Bits (Z_to_bv 64 (freeReturnAddress args)) ∗
   "x2" ↦ᵣ RVal_Bits (Z_to_bv 64 (freeStackPointer args)) ∗
   "x8" ↦ᵣ RVal_Bits (freeSavedFramePointer args) ∗
   "x10" ↦ᵣ RVal_Bits x10 ∗
   "x11" ↦ᵣ RVal_Bits (Z_to_bv 64 (freeBufferPointer args)) ∗
   "x12" ↦ᵣ RVal_Bits x12 ∗ "x13" ↦ᵣ RVal_Bits x13 ∗
   "x14" ↦ᵣ RVal_Bits x14 ∗
   (freeStackPointer args - freeStackBytes) ↦ₘ? freeStackBytes ∗ True)%I.

Definition freeExitResources `{!islaG Sigma} `{!threadG}
    (args : FreeArgs) (after : FreeOutcome) : iProp Sigma :=
  (freeBufferPointer args ↦ₘ∗ freeAfterBuffer after ∗
   freeListsPointer ↦ₘ∗ freeAfterLists after ∗ freeExitRegisterResources args)%I.

Definition freeResources `{!islaG Sigma} `{!threadG} (code : iProp Sigma) :
    IslarisContractResources FreeArgs FreeOutcome :=
  {| islarisCode := code;
     islarisEntry := freeEntryResources;
     islarisExit := freeExitResources |}.

Definition freeDomainAt (returnAddress : Z) (args : FreeArgs) : Prop :=
  freeReturnAddress args = returnAddress /\ freeArgsWellFormed args.
Definition freeAllowsAt (returnAddress : Z) (args : FreeArgs)
    (after : FreeOutcome) : Prop :=
  freeDomainAt returnAddress args /\ freeAllows args after.

(* The generator will provide the code resource. This interface does not assume a run. *)
Definition freeModel (returnAddress : Z)
    (code : forall (Sigma : gFunctors), islaG Sigma -> threadG -> iProp Sigma) :
    IslarisContractModel FreeArgs FreeOutcome :=
  {| islarisContractAllows := freeAllowsAt returnAddress;
     islarisContractStep := freeCfgStep;
     islarisContractResources := fun Sigma HG HT =>
       {| islarisCode := code Sigma HG HT;
          islarisEntry := fun args =>
            (⌜freeReturnAddress args = returnAddress⌝ ∗ freeEntryResources args)%I;
          islarisExit := freeExitResources |} |}.

Definition FreeComplianceStatement
    (code : forall (Sigma : gFunctors), islaG Sigma -> threadG -> iProp Sigma) : Prop :=
  forall returnAddress,
    IslarisContractCorrect freeEntry returnAddress (freeModel returnAddress code).
