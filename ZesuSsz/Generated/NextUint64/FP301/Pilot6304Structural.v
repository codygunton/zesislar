(* Rendered from the checked entry ZesuSsz.Contracts.NextUint64BlockEntries.nextUint64EntryAt800d6304. No proof script. *)
Require ZesuSsz.Automation.Hooks.
Require Import isla.riscv64.riscv64.
From Coq Require Import Lists.List ZArith.ZArith NArith.NArith.
Require Import stdpp.bitvector.definitions.
Require Import EvmSailRlp.evm_rlp_types.
Require Import ZesuSsz.Contracts.RlpDecodeItem.
Require Import ZesuSsz.Contracts.AbiBytes.
Require Import ZesuSsz.Contracts.RlpDecodeItemContract.
Require Import ZesuSsz.Contracts.ParentHeaderRootFacts.
Require Import ZesuSsz.Contracts.NextUint64BlockEntries.
Local Open Scope Z_scope.
Require Export ZesuSsz.Generated.NextUint64.FP301.EntryHelpers.
Require Import ZesuSsz.Generated.NextUint64.FP301.Pilot6304Entries.
#[export] Instance fp_machineAt6304_unfold : LithiumUnfold (@fp_machineAt6304) := I.
#[export] Typeclasses Opaque fp_machineAt6304.
#[export] Instance fp_machineAt6304_intro `{!islaG Sigma} `{!threadG} (params : NextUint64Args) (returnAddress : Z) (K : iProp Sigma) :
  @ZesuSsz.Automation.Hooks.ZesuPureFactIntro Sigma (fp_machineAt6304 (params) (returnAddress) (K))
  ((∃ (x1 x2 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 : bv 64) (inputBytes sliceBytes decoded saved : list byte), (  let args := nextUint64Base params in
  (reg_col (nextUint64SysRegs params) ∗
   (("x1" ↦ᵣ RVal_Bits x1 ∗
   "x2" ↦ᵣ RVal_Bits x2 ∗
   "x5" ↦ᵣ RVal_Bits x5 ∗
   "x6" ↦ᵣ RVal_Bits x6 ∗
   "x7" ↦ᵣ RVal_Bits x7 ∗
   "x8" ↦ᵣ RVal_Bits x8 ∗
   "x9" ↦ᵣ RVal_Bits x9 ∗
   "x10" ↦ᵣ RVal_Bits x10 ∗
   "x11" ↦ᵣ RVal_Bits x11 ∗
   "x12" ↦ᵣ RVal_Bits x12 ∗
   "x13" ↦ᵣ RVal_Bits x13 ∗
   "x14" ↦ᵣ RVal_Bits x14 ∗
   "x15" ↦ᵣ RVal_Bits x15 ∗
   "x16" ↦ᵣ RVal_Bits x16 ∗
   "x17" ↦ᵣ RVal_Bits x17 ∗
   "x18" ↦ᵣ RVal_Bits x18 ∗
   "x19" ↦ᵣ RVal_Bits x19 ∗
   "x20" ↦ᵣ RVal_Bits x20 ∗
   "x21" ↦ᵣ RVal_Bits x21 ∗
   "x22" ↦ᵣ RVal_Bits x22 ∗
   "x23" ↦ᵣ RVal_Bits x23 ∗
   "x24" ↦ᵣ RVal_Bits x24 ∗
   "x25" ↦ᵣ RVal_Bits x25 ∗
   "x26" ↦ᵣ RVal_Bits x26 ∗
   "x27" ↦ᵣ RVal_Bits x27 ∗
   "x28" ↦ᵣ RVal_Bits x28 ∗
   "x29" ↦ᵣ RVal_Bits x29 ∗
   "x30" ↦ᵣ RVal_Bits x30 ∗
   "x31" ↦ᵣ RVal_Bits x31)%I) ∗
   ((nextInputPointer args ↦ₘ∗ inputBytes ∗
   nextSlicePointer args ↦ₘ∗ sliceBytes ∗
   (nextStackPointer args - 96) ↦ₘ? 8 ∗
   (nextStackPointer args - 88) ↦ₘ∗ decoded ∗
   (nextStackPointer args - 48) ↦ₘ∗ saved ∗
   (nextStackPointer args - 112) ↦ₘ? 16)%I) ∗
   nextResultPointer args ↦ₘ? 16 ∗
   ⌜(nextUint64BoundaryDomain params /\ inputBytes = nextInputBytes args /\
  length decoded = 40%nat /\ nextUint64SavedFrameFacts args saved /\
  x1 = Z_to_bv 64 0x800d62b8 /\
  x2 = Z_to_bv 64 (nextStackPointer args - 96) /\
  x8 = Z_to_bv 64 (nextStackPointer args) /\
  x9 = Z_to_bv 64 (nextResultPointer args) /\
  x18 = Z_to_bv 64 (nextSlicePointer args) /\
  x20 = Z_to_bv 64 (Z.of_nat (length (nextInputBytes args))) /\
  x21 = nextUint64SavedX21 params /\
  x22 = nextUint64SavedX22 params /\
  x23 = nextUint64SavedX23 params /\
  x24 = nextUint64SavedX24 params /\
  x25 = nextUint64SavedX25 params /\
  x26 = nextUint64SavedX26 params /\
  x27 = nextUint64SavedX27 params) /\
     x19 = Z_to_bv 64 (nextInputPointer args) /\
     sliceBytes = nextUint64SliceImage (nextInputPointer args) (Z.of_nat (length (nextInputBytes args))) /\
     nextUint64AcceptedBytes args decoded /\
     bv_unsigned x13 = nextUint64DecodedLength decoded /\
     x10 = Z_to_bv 64 8⌝ ∗ True)%I)) ∗ K)%I := @PreOrder_Reflexive _ _ bi.entails_po _.

#[export] Instance nextUint64EntryAt800d6304_unfold : LithiumUnfold (@ZesuSsz.Contracts.NextUint64BlockEntries.nextUint64EntryAt800d6304) := I.
#[export] Typeclasses Opaque ZesuSsz.Contracts.NextUint64BlockEntries.nextUint64EntryAt800d6304.
#[export] Instance nextUint64EntryAt800d6304_intro `{!islaG Sigma} `{!threadG} (params : NextUint64Args) (x1 x2 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 : bv 64) (inputBytes sliceBytes decoded saved : list byte) :
  @ZesuSsz.Automation.Hooks.ZesuPureFactIntro Sigma (ZesuSsz.Contracts.NextUint64BlockEntries.nextUint64EntryAt800d6304 params x1 x2 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 inputBytes sliceBytes decoded saved)
  (  let args := nextUint64Base params in
  (reg_col (nextUint64SysRegs params) ∗
   (("x1" ↦ᵣ RVal_Bits x1 ∗
   "x2" ↦ᵣ RVal_Bits x2 ∗
   "x5" ↦ᵣ RVal_Bits x5 ∗
   "x6" ↦ᵣ RVal_Bits x6 ∗
   "x7" ↦ᵣ RVal_Bits x7 ∗
   "x8" ↦ᵣ RVal_Bits x8 ∗
   "x9" ↦ᵣ RVal_Bits x9 ∗
   "x10" ↦ᵣ RVal_Bits x10 ∗
   "x11" ↦ᵣ RVal_Bits x11 ∗
   "x12" ↦ᵣ RVal_Bits x12 ∗
   "x13" ↦ᵣ RVal_Bits x13 ∗
   "x14" ↦ᵣ RVal_Bits x14 ∗
   "x15" ↦ᵣ RVal_Bits x15 ∗
   "x16" ↦ᵣ RVal_Bits x16 ∗
   "x17" ↦ᵣ RVal_Bits x17 ∗
   "x18" ↦ᵣ RVal_Bits x18 ∗
   "x19" ↦ᵣ RVal_Bits x19 ∗
   "x20" ↦ᵣ RVal_Bits x20 ∗
   "x21" ↦ᵣ RVal_Bits x21 ∗
   "x22" ↦ᵣ RVal_Bits x22 ∗
   "x23" ↦ᵣ RVal_Bits x23 ∗
   "x24" ↦ᵣ RVal_Bits x24 ∗
   "x25" ↦ᵣ RVal_Bits x25 ∗
   "x26" ↦ᵣ RVal_Bits x26 ∗
   "x27" ↦ᵣ RVal_Bits x27 ∗
   "x28" ↦ᵣ RVal_Bits x28 ∗
   "x29" ↦ᵣ RVal_Bits x29 ∗
   "x30" ↦ᵣ RVal_Bits x30 ∗
   "x31" ↦ᵣ RVal_Bits x31)%I) ∗
   ((nextInputPointer args ↦ₘ∗ inputBytes ∗
   nextSlicePointer args ↦ₘ∗ sliceBytes ∗
   (nextStackPointer args - 96) ↦ₘ? 8 ∗
   (nextStackPointer args - 88) ↦ₘ∗ decoded ∗
   (nextStackPointer args - 48) ↦ₘ∗ saved ∗
   (nextStackPointer args - 112) ↦ₘ? 16)%I) ∗
   nextResultPointer args ↦ₘ? 16 ∗
   ⌜(nextUint64BoundaryDomain params /\ inputBytes = nextInputBytes args /\
  length decoded = 40%nat /\ nextUint64SavedFrameFacts args saved /\
  x1 = Z_to_bv 64 0x800d62b8 /\
  x2 = Z_to_bv 64 (nextStackPointer args - 96) /\
  x8 = Z_to_bv 64 (nextStackPointer args) /\
  x9 = Z_to_bv 64 (nextResultPointer args) /\
  x18 = Z_to_bv 64 (nextSlicePointer args) /\
  x20 = Z_to_bv 64 (Z.of_nat (length (nextInputBytes args))) /\
  x21 = nextUint64SavedX21 params /\
  x22 = nextUint64SavedX22 params /\
  x23 = nextUint64SavedX23 params /\
  x24 = nextUint64SavedX24 params /\
  x25 = nextUint64SavedX25 params /\
  x26 = nextUint64SavedX26 params /\
  x27 = nextUint64SavedX27 params) /\
     x19 = Z_to_bv 64 (nextInputPointer args) /\
     sliceBytes = nextUint64SliceImage (nextInputPointer args) (Z.of_nat (length (nextInputBytes args))) /\
     nextUint64AcceptedBytes args decoded /\
     bv_unsigned x13 = nextUint64DecodedLength decoded /\
     x10 = Z_to_bv 64 8⌝ ∗ True)%I) := @PreOrder_Reflexive _ _ bi.entails_po _.
