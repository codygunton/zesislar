From Coq Require Import List ZArith.
From stdpp Require Import bitvector.definitions.
Require Import EvmSailRlp.evm_rlp_types.
Require Import isla.riscv64.riscv64.
Require Import InstrSpecs.Machine.
Require Import ZesuStock.CalleeIdentity.
Require Import ZesuSsz.Stock.Closure.index_decodeParentHeader.
Require Import ZesuSsz.Stock.Closure.index_memcpyStub.
Require Import ZesuSsz.Stock.Closure.index_nextUint64.
Require Import ZesuSsz.Contracts.AbiBytes.
Require Import ZesuSsz.Contracts.DecodeItemSelected.
Require Import ZesuSsz.Contracts.Level1.
Require Import ZesuSsz.Contracts.NextUint64Selected.
Require Import ZesuSsz.Contracts.ParentHeader.
Require Import ZesuSsz.Contracts.ParentHeaderLevel1.
Require Import ZesuSsz.Contracts.ParentHeaderMemcpyService.
Require Import ZesuSsz.Contracts.ParentHeaderRootFacts.
Require Import ZesuSsz.Contracts.ParentHeaderRung2.
Require Import ZesuSsz.Contracts.ZiskRuntime.

Open Scope Z_scope.

Inductive ParentHeaderExitPath :=
| ParentHeaderDirect
| ParentHeaderMemcpyTail.

Record ParentHeaderSelectedOutcome := {
  headerExitPath : ParentHeaderExitPath;
  headerResultBytes : list byte;
  headerAfterFrame : list byte
}.

Definition parentHeaderSelectedAllows
    (args : ParentHeaderCall) (outcome : ParentHeaderSelectedOutcome) : Prop :=
  ParentHeaderMeaningModuloKnownBugs args outcome.(headerResultBytes) /\
  List.length outcome.(headerAfterFrame) = 400%nat /\
  match outcome.(headerExitPath) with
  | ParentHeaderDirect => True
  | ParentHeaderMemcpyTail =>
      outcome.(headerResultBytes) = args.(headerMemcpySourceBefore)
  end.

Definition parentHeaderSelectedCode `{!islaG Sigma} `{!threadG} :
    iProp Sigma :=
  (([∗ list] instruction ∈
     ZesuSsz.Stock.Closure.index_decodeParentHeader.instr_map,
     instr instruction.1 (Some instruction.2)) ∗
   nextUint64SelectedCode ∗
   ([∗ list] instruction ∈
     ZesuSsz.Stock.Closure.index_memcpyStub.instr_map,
     instr instruction.1 (Some instruction.2)) ∗
   memcpyServicePremise)%I.

Definition parentHeaderSelectedEntry `{!islaG Sigma} `{!threadG}
    (returnAddress : Z) (args : ParentHeaderCall) : iProp Sigma :=
  (reg_col zesu_sys_regs ∗
   "x10" ↦ᵣ RVal_Bits (Z_to_bv 64 args.(headerResultPointer)) ∗
   "x11" ↦ᵣ RVal_Bits (Z_to_bv 64 args.(headerInputPointer)) ∗
   "x12" ↦ᵣ RVal_Bits
     (Z_to_bv 64 (Z.of_nat (List.length args.(headerInputBytes)))) ∗
   "x2" ↦ᵣ RVal_Bits (Z_to_bv 64 args.(headerStackPointer)) ∗
   "x1" ↦ᵣ RVal_Bits (Z_to_bv 64 args.(headerReturnAddress)) ∗
   "x8" ↦ᵣ RVal_Bits args.(headerSavedS0) ∗
   "x9" ↦ᵣ RVal_Bits args.(headerSavedS1) ∗
   "x18" ↦ᵣ RVal_Bits args.(headerSavedS2) ∗
   "x19" ↦ᵣ RVal_Bits args.(headerSavedS3) ∗
   "x20" ↦ᵣ RVal_Bits args.(headerSavedS4) ∗
   "x21" ↦ᵣ RVal_Bits args.(headerSavedS5) ∗
   "x22" ↦ᵣ RVal_Bits args.(headerSavedS6) ∗
   "x23" ↦ᵣ RVal_Bits args.(headerSavedS7) ∗
   "x24" ↦ᵣ RVal_Bits args.(headerSavedS8) ∗
   args.(headerInputPointer) ↦ₘ∗ args.(headerInputBytes) ∗
   args.(headerResultPointer) ↦ₘ? 80 ∗
   (args.(headerStackPointer) - parentHeaderStackBytes) ↦ₘ∗
     args.(headerBeforeFrame) ∗
   parentHeaderMemcpySource ↦ₘ∗ args.(headerMemcpySourceBefore) ∗
   ziskExtraParamsAddress ↦ₘ∗ args.(headerMemcpyScratchBefore) ∗
   ⌜args.(headerReturnAddress) = returnAddress /\
     parentHeaderDomain args /\
     List.length args.(headerBeforeFrame) = 400%nat /\
     List.length args.(headerMemcpySourceBefore) = 80%nat /\
     List.length args.(headerMemcpyScratchBefore) = 8%nat /\
     parentHeaderError80 args.(headerMemcpySourceBefore)⌝ ∗ True)%I.

Definition parentHeaderScratchAfter (args : ParentHeaderCall)
    (path : ParentHeaderExitPath) : list byte :=
  match path with
  | ParentHeaderDirect => args.(headerMemcpyScratchBefore)
  | ParentHeaderMemcpyTail => word64Bytes parentHeaderMemcpyLength
  end.

Definition parentHeaderSelectedExit `{!islaG Sigma} `{!threadG}
    (args : ParentHeaderCall) (outcome : ParentHeaderSelectedOutcome) :
    iProp Sigma :=
  (reg_col zesu_sys_regs ∗
   "x2" ↦ᵣ RVal_Bits (Z_to_bv 64 args.(headerStackPointer)) ∗
   "x1" ↦ᵣ RVal_Bits (Z_to_bv 64 args.(headerReturnAddress)) ∗
   "x8" ↦ᵣ RVal_Bits args.(headerSavedS0) ∗
   "x9" ↦ᵣ RVal_Bits args.(headerSavedS1) ∗
   "x18" ↦ᵣ RVal_Bits args.(headerSavedS2) ∗
   "x19" ↦ᵣ RVal_Bits args.(headerSavedS3) ∗
   "x20" ↦ᵣ RVal_Bits args.(headerSavedS4) ∗
   "x21" ↦ᵣ RVal_Bits args.(headerSavedS5) ∗
   "x22" ↦ᵣ RVal_Bits args.(headerSavedS6) ∗
   "x23" ↦ᵣ RVal_Bits args.(headerSavedS7) ∗
   "x24" ↦ᵣ RVal_Bits args.(headerSavedS8) ∗
   args.(headerInputPointer) ↦ₘ∗ args.(headerInputBytes) ∗
   args.(headerResultPointer) ↦ₘ∗ outcome.(headerResultBytes) ∗
   (args.(headerStackPointer) - parentHeaderStackBytes) ↦ₘ∗
     outcome.(headerAfterFrame) ∗
   parentHeaderMemcpySource ↦ₘ∗ args.(headerMemcpySourceBefore) ∗
   ziskExtraParamsAddress ↦ₘ∗
     parentHeaderScratchAfter args outcome.(headerExitPath) ∗ True)%I.

Definition parentHeaderSelectedResources `{!islaG Sigma} `{!threadG}
    (returnAddress : Z) :
    IslarisContractResources ParentHeaderCall ParentHeaderSelectedOutcome :=
  {| islarisCode := parentHeaderSelectedCode;
     islarisEntry := parentHeaderSelectedEntry returnAddress;
     islarisExit := parentHeaderSelectedExit |}.

Definition parentHeaderSelectedModel (returnAddress : Z) :
    IslarisContractModel ParentHeaderCall ParentHeaderSelectedOutcome :=
  {| islarisContractAllows := fun args outcome =>
       args.(headerReturnAddress) = returnAddress /\
       parentHeaderSelectedAllows args outcome;
     islarisContractStep := fun source target =>
       ZesuSsz.Stock.Closure.index_decodeParentHeader.decodeParentHeader_cfg_step
         source target \/
       ZesuSsz.Stock.Closure.index_nextUint64.nextUint64_cfg_step
         source target \/
       ZesuSsz.Stock.Closure.index_decodeItem.decodeItem_cfg_step
         source target \/
       ZesuSsz.Stock.Closure.index_memcpyStub.memcpyStub_cfg_step
         source target;
     islarisContractResources := fun Sigma HG HT =>
       @parentHeaderSelectedResources Sigma HG HT returnAddress |}.

Definition ParentHeaderSelectedCorrect : Prop :=
  forall returnAddress,
    IslarisContractCorrect decodeParentHeaderEntry returnAddress
      (parentHeaderSelectedModel returnAddress).
