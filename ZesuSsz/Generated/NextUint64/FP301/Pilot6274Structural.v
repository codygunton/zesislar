(* Rendered from the checked entry ZesuSsz.Contracts.NextUint64BlockEntries.nextUint64EntryAt800d6274. No proof script. *)
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
Require Import ZesuSsz.Generated.NextUint64.FP301.Pilot6274Entries.
#[export] Instance fp_machineAt6274_unfold : LithiumUnfold (@fp_machineAt6274) := I.
#[export] Typeclasses Opaque fp_machineAt6274.
#[export] Instance fp_machineAt6274_intro `{!islaG Sigma} `{!threadG} (args : NextUint64Args) (returnAddress : Z) (K : iProp Sigma) :
  @ZesuSsz.Automation.Hooks.ZesuPureFactIntro Sigma (fp_machineAt6274 (args) (returnAddress) (K))
  ((∃ (x1 x2 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 : bv 64) (inputBytes sliceBytes : list byte), ZesuSsz.Contracts.NextUint64BlockEntries.nextUint64EntryAt800d6274 (args) x1 x2 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 inputBytes sliceBytes) ∗ K)%I := @PreOrder_Reflexive _ _ bi.entails_po _.

#[export] Instance nextUint64EntryAt800d6274_unfold : LithiumUnfold (@ZesuSsz.Contracts.NextUint64BlockEntries.nextUint64EntryAt800d6274) := I.
#[export] Typeclasses Opaque ZesuSsz.Contracts.NextUint64BlockEntries.nextUint64EntryAt800d6274.
#[export] Instance nextUint64EntryAt800d6274_intro `{!islaG Sigma} `{!threadG} (params : NextUint64Args) (x1 x2 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 : bv 64) (inputBytes sliceBytes : list byte) :
  @ZesuSsz.Automation.Hooks.ZesuPureFactIntro Sigma (ZesuSsz.Contracts.NextUint64BlockEntries.nextUint64EntryAt800d6274 params x1 x2 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 inputBytes sliceBytes)
  (  let args := nextUint64Base params in
  (reg_col (nextUint64SysRegs params) ∗
   nextUint64Registers x1 x2 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 ∗
   nextInputPointer args ↦ₘ∗ inputBytes ∗
   nextSlicePointer args ↦ₘ∗ sliceBytes ∗
   nextResultPointer args ↦ₘ? 16 ∗
   (nextStackPointer args - 96) ↦ₘ? 96 ∗
   (nextStackPointer args - 112) ↦ₘ? 16 ∗
   ⌜nextUint64BoundaryDomain params /\
     inputBytes = nextInputBytes args /\
     sliceBytes = nextUint64SliceImage (nextInputPointer args) (Z.of_nat (length (nextInputBytes args))) /\
     x1 = Z_to_bv 64 (nextReturnAddress args) /\
     x2 = Z_to_bv 64 (nextStackPointer args) /\
     x8 = nextSavedS0 args /\
     x9 = nextSavedS1 args /\
     x10 = Z_to_bv 64 (nextResultPointer args) /\
     x11 = Z_to_bv 64 (nextSlicePointer args) /\
     x18 = nextSavedS2 args /\
     x19 = nextSavedS3 args /\
     x20 = nextSavedS4 args /\
     x21 = nextUint64SavedX21 params /\
     x22 = nextUint64SavedX22 params /\
     x23 = nextUint64SavedX23 params /\
     x24 = nextUint64SavedX24 params /\
     x25 = nextUint64SavedX25 params /\
     x26 = nextUint64SavedX26 params /\
     x27 = nextUint64SavedX27 params⌝ ∗ True)%I) := @PreOrder_Reflexive _ _ bi.entails_po _.
