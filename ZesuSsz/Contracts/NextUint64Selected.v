From Coq Require Import List ZArith.
From stdpp Require Import bitvector.definitions.
Require Import EvmSailRlp.evm_rlp_types.
Require Import isla.riscv64.riscv64.
Require Import InstrSpecs.Machine.
Require Import ZesuStock.CalleeIdentity.
Require Import ZesuSsz.Stock.Closure.index_nextUint64.
Require Import ZesuSsz.Contracts.AbiBytes.
Require Import ZesuSsz.Contracts.DecodeItemSelected.
Require Import ZesuSsz.Contracts.Level1.
Require Import ZesuSsz.Contracts.ParentHeader.
Require Import ZesuSsz.Contracts.ParentHeaderLevel1.
Require Import ZesuSsz.Contracts.ParentHeaderRootFacts.

Open Scope Z_scope.

Definition nextUint64SelectedCode `{!islaG Sigma} `{!threadG} : iProp Sigma :=
  (([∗ list] instruction ∈
     ZesuSsz.Stock.Closure.index_nextUint64.instr_map,
     instr instruction.1 (Some instruction.2)) ∗
   decodeItemSelectedCode)%I.

Definition nextUint64SliceBefore (args : NextUint64Call) : list byte :=
  word64Bytes args.(nextInputPointer) ++
  word64Bytes (Z.of_nat (List.length args.(nextInputBytes))).

Definition nextUint64SliceAfter (result : NextUint64Return) : list byte :=
  word64Bytes result.(nextRestPointer) ++
  word64Bytes result.(nextRestLength).

Definition nextUint64SelectedEntry `{!islaG Sigma} `{!threadG}
    (returnAddress : Z) (args : NextUint64Call) : iProp Sigma :=
  (reg_col zesu_sys_regs ∗
   "x10" ↦ᵣ RVal_Bits (Z_to_bv 64 args.(nextResultPointer)) ∗
   "x11" ↦ᵣ RVal_Bits (Z_to_bv 64 args.(nextSlicePointer)) ∗
   "x2" ↦ᵣ RVal_Bits (Z_to_bv 64 args.(nextStackPointer)) ∗
   "x1" ↦ᵣ RVal_Bits (Z_to_bv 64 args.(nextReturnAddress)) ∗
   "x8" ↦ᵣ RVal_Bits args.(nextSavedS0) ∗
   "x9" ↦ᵣ RVal_Bits args.(nextSavedS1) ∗
   "x18" ↦ᵣ RVal_Bits args.(nextSavedS2) ∗
   "x19" ↦ᵣ RVal_Bits args.(nextSavedS3) ∗
   "x20" ↦ᵣ RVal_Bits args.(nextSavedS4) ∗
   args.(nextInputPointer) ↦ₘ∗ args.(nextInputBytes) ∗
   args.(nextSlicePointer) ↦ₘ∗ nextUint64SliceBefore args ∗
   args.(nextResultPointer) ↦ₘ? 16 ∗
   (args.(nextStackPointer) - nextUint64StackBytes) ↦ₘ?
     nextUint64StackBytes ∗
   ⌜args.(nextReturnAddress) = returnAddress /\
     nextUint64Domain args⌝ ∗ True)%I.

Definition nextUint64SelectedExit `{!islaG Sigma} `{!threadG}
    (args : NextUint64Call) (result : NextUint64Return) : iProp Sigma :=
  (reg_col zesu_sys_regs ∗
   "x2" ↦ᵣ RVal_Bits (Z_to_bv 64 args.(nextStackPointer)) ∗
   "x1" ↦ᵣ RVal_Bits (Z_to_bv 64 args.(nextReturnAddress)) ∗
   "x8" ↦ᵣ RVal_Bits args.(nextSavedS0) ∗
   "x9" ↦ᵣ RVal_Bits args.(nextSavedS1) ∗
   "x18" ↦ᵣ RVal_Bits args.(nextSavedS2) ∗
   "x19" ↦ᵣ RVal_Bits args.(nextSavedS3) ∗
   "x20" ↦ᵣ RVal_Bits args.(nextSavedS4) ∗
   args.(nextInputPointer) ↦ₘ∗ args.(nextInputBytes) ∗
   args.(nextSlicePointer) ↦ₘ∗ nextUint64SliceAfter result ∗
   args.(nextResultPointer) ↦ₘ∗ result.(nextResultBytes) ∗
   (args.(nextStackPointer) - nextUint64StackBytes) ↦ₘ?
     nextUint64StackBytes ∗ True)%I.

Definition nextUint64SelectedResources `{!islaG Sigma} `{!threadG}
    (returnAddress : Z) :
    IslarisContractResources NextUint64Call NextUint64Return :=
  {| islarisCode := nextUint64SelectedCode;
     islarisEntry := nextUint64SelectedEntry returnAddress;
     islarisExit := nextUint64SelectedExit |}.

Definition nextUint64SelectedModel (returnAddress : Z) :
    IslarisContractModel NextUint64Call NextUint64Return :=
  {| islarisContractAllows := fun args result =>
       args.(nextReturnAddress) = returnAddress /\
       nextUint64Allows args result;
     islarisContractStep := fun source target =>
       ZesuSsz.Stock.Closure.index_nextUint64.nextUint64_cfg_step
         source target \/
       ZesuSsz.Stock.Closure.index_decodeItem.decodeItem_cfg_step
         source target;
     islarisContractResources := fun Sigma HG HT =>
       @nextUint64SelectedResources Sigma HG HT returnAddress |}.

Definition NextUint64SelectedCorrect : Prop :=
  forall returnAddress,
    IslarisContractCorrect nextUint64Entry returnAddress
      (nextUint64SelectedModel returnAddress).
