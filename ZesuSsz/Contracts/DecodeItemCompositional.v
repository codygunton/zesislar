From Coq Require Import List ZArith.
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Contracts.Level1.
Require Import ZesuSsz.Contracts.RlpDecodeItemContract.
Require Import ZesuSsz.Contracts.DecodeItemSelected.
Open Scope Z_scope.

(* The existing native entry owns these seven caller-saved registers. *)
Definition decodeItemReturnedCallerRegisters `{!islaG Sigma} `{!threadG} : iProp Sigma :=
  (∃ (x10 x11 x12 x13 x14 x15 x16 : bv 64),
   "x10" ↦ᵣ RVal_Bits x10 ∗ "x11" ↦ᵣ RVal_Bits x11 ∗
   "x12" ↦ᵣ RVal_Bits x12 ∗ "x13" ↦ᵣ RVal_Bits x13 ∗
   "x14" ↦ᵣ RVal_Bits x14 ∗ "x15" ↦ᵣ RVal_Bits x15 ∗
   "x16" ↦ᵣ RVal_Bits x16)%I.

(* The native core does not own or access these additional caller-saved registers. *)
Definition decodeItemOtherCallerRegisters `{!islaG Sigma} `{!threadG} : iProp Sigma :=
  (∃ (x5 x6 x7 x17 x28 x29 x30 x31 : bv 64),
   "x5" ↦ᵣ RVal_Bits x5 ∗ "x6" ↦ᵣ RVal_Bits x6 ∗
   "x7" ↦ᵣ RVal_Bits x7 ∗ "x17" ↦ᵣ RVal_Bits x17 ∗
   "x28" ↦ᵣ RVal_Bits x28 ∗ "x29" ↦ᵣ RVal_Bits x29 ∗
   "x30" ↦ᵣ RVal_Bits x30 ∗ "x31" ↦ᵣ RVal_Bits x31)%I.

Record DecodeItemOtherCalleeSaved : Type := {
  decodeItemSavedX9 : bv 64;
  decodeItemSavedX18 : bv 64;
  decodeItemSavedX19 : bv 64;
  decodeItemSavedX20 : bv 64;
  decodeItemSavedX21 : bv 64;
  decodeItemSavedX22 : bv 64;
  decodeItemSavedX23 : bv 64;
  decodeItemSavedX24 : bv 64;
  decodeItemSavedX25 : bv 64;
  decodeItemSavedX26 : bv 64;
  decodeItemSavedX27 : bv 64
}.

Definition decodeItemOtherCalleeRegisters `{!islaG Sigma} `{!threadG}
    (saved : DecodeItemOtherCalleeSaved) : iProp Sigma :=
  ("x9" ↦ᵣ RVal_Bits (decodeItemSavedX9 saved) ∗
   "x18" ↦ᵣ RVal_Bits (decodeItemSavedX18 saved) ∗
   "x19" ↦ᵣ RVal_Bits (decodeItemSavedX19 saved) ∗
   "x20" ↦ᵣ RVal_Bits (decodeItemSavedX20 saved) ∗
   "x21" ↦ᵣ RVal_Bits (decodeItemSavedX21 saved) ∗
   "x22" ↦ᵣ RVal_Bits (decodeItemSavedX22 saved) ∗
   "x23" ↦ᵣ RVal_Bits (decodeItemSavedX23 saved) ∗
   "x24" ↦ᵣ RVal_Bits (decodeItemSavedX24 saved) ∗
   "x25" ↦ᵣ RVal_Bits (decodeItemSavedX25 saved) ∗
   "x26" ↦ᵣ RVal_Bits (decodeItemSavedX26 saved) ∗
   "x27" ↦ᵣ RVal_Bits (decodeItemSavedX27 saved))%I.

Definition decodeItemUntouchedRegisters `{!islaG Sigma} `{!threadG}
    (saved : DecodeItemOtherCalleeSaved) : iProp Sigma :=
  (decodeItemOtherCallerRegisters ∗ decodeItemOtherCalleeRegisters saved)%I.

(* This core strengthening requires exactly the existing native entry resources. *)
Definition decodeItemExitResourcesRegisters `{!islaG Sigma} `{!threadG}
    (args : DecodeItemArgs) (after : DecodeItemOutcome) : iProp Sigma :=
  (decodeItemExitResources args after ∗ decodeItemReturnedCallerRegisters)%I.

Record DecodeItemCompositionalArgs : Type := {
  decodeItemCompositionalBase : DecodeItemArgs;
  decodeItemCompositionalSaved : DecodeItemOtherCalleeSaved
}.

Definition decodeItemEntryResourcesCompositional `{!islaG Sigma} `{!threadG}
    (domain : DecodeItemArgs -> Prop) (args : DecodeItemCompositionalArgs) : iProp Sigma :=
  (decodeItemEntryResources domain (decodeItemCompositionalBase args) ∗
   decodeItemUntouchedRegisters (decodeItemCompositionalSaved args))%I.

(* The base exit returns x1, x2, x8, both arrays, and the saved frame.
   This extension returns every other ABI caller/callee register. *)
Definition decodeItemExitResourcesCompositional `{!islaG Sigma} `{!threadG}
    (args : DecodeItemCompositionalArgs) (after : DecodeItemOutcome) : iProp Sigma :=
  (decodeItemExitResourcesRegisters (decodeItemCompositionalBase args) after ∗
   decodeItemUntouchedRegisters (decodeItemCompositionalSaved args))%I.

Definition decodeItemResourcesRegisters `{!islaG Sigma} `{!threadG}
    (code : iProp Sigma) (domain : DecodeItemArgs -> Prop) :
    IslarisContractResources DecodeItemArgs DecodeItemOutcome :=
  {| islarisCode := code;
     islarisEntry := decodeItemEntryResources domain;
     islarisExit := decodeItemExitResourcesRegisters |}.

Definition decodeItemResourcesCompositional `{!islaG Sigma} `{!threadG}
    (code : iProp Sigma) (domain : DecodeItemArgs -> Prop) :
    IslarisContractResources DecodeItemCompositionalArgs DecodeItemOutcome :=
  {| islarisCode := code;
     islarisEntry := decodeItemEntryResourcesCompositional domain;
     islarisExit := decodeItemExitResourcesCompositional |}.

Definition decodeItemSelectedModelRegisters (returnAddress : Z) :
    IslarisContractModel DecodeItemArgs DecodeItemOutcome :=
  {| islarisContractAllows := fun args after =>
       decodeItemDomainAt returnAddress decodeItemC1BDomain args /\
       DecodeMeaningModuloKnownBugs args after;
     islarisContractStep :=
       ZesuSsz.Stock.Closure.index_decodeItem.decodeItem_cfg_step;
     islarisContractResources := fun Sigma HG HT =>
       decodeItemResourcesRegisters (decodeItemSelectedCode (Sigma:=Sigma))
         (decodeItemDomainAt returnAddress decodeItemC1BDomain) |}.

Definition decodeItemSelectedModelCompositional (returnAddress : Z) :
    IslarisContractModel DecodeItemCompositionalArgs DecodeItemOutcome :=
  {| islarisContractAllows := fun args after =>
       decodeItemDomainAt returnAddress decodeItemC1BDomain
         (decodeItemCompositionalBase args) /\
       DecodeMeaningModuloKnownBugs (decodeItemCompositionalBase args) after;
     islarisContractStep :=
       ZesuSsz.Stock.Closure.index_decodeItem.decodeItem_cfg_step;
     islarisContractResources := fun Sigma HG HT =>
       decodeItemResourcesCompositional (decodeItemSelectedCode (Sigma:=Sigma))
         (decodeItemDomainAt returnAddress decodeItemC1BDomain) |}.
