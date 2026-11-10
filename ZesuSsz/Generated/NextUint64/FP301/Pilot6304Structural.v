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
#[export] Instance fp_machineAt6304_intro `{!islaG Sigma} `{!threadG} (args : NextUint64Args) (returnAddress : Z) (K : iProp Sigma) :
  @ZesuSsz.Automation.Hooks.ZesuPureFactIntro Sigma (fp_machineAt6304 (args) (returnAddress) (K))
  ((∃ (x1 x2 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 : bv 64) (inputBytes sliceBytes decoded saved : list byte), ZesuSsz.Contracts.NextUint64BlockEntries.nextUint64EntryAt800d6304 (args) x1 x2 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 inputBytes sliceBytes decoded saved) ∗ K)%I := @PreOrder_Reflexive _ _ bi.entails_po _.

#[export] Instance nextUint64EntryAt800d6304_unfold : LithiumUnfold (@ZesuSsz.Contracts.NextUint64BlockEntries.nextUint64EntryAt800d6304) := I.
#[export] Typeclasses Opaque ZesuSsz.Contracts.NextUint64BlockEntries.nextUint64EntryAt800d6304.
#[export] Instance nextUint64EntryAt800d6304_intro `{!islaG Sigma} `{!threadG} (params : NextUint64Args) (x1 x2 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 : bv 64) (inputBytes sliceBytes decoded saved : list byte) :
  @ZesuSsz.Automation.Hooks.ZesuPureFactIntro Sigma (ZesuSsz.Contracts.NextUint64BlockEntries.nextUint64EntryAt800d6304 params x1 x2 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 inputBytes sliceBytes decoded saved)
  (  let args := nextUint64Base params in
  (reg_col (nextUint64SysRegs params) ∗
   nextUint64Registers x1 x2 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 ∗
   nextUint64PostMemory params inputBytes sliceBytes decoded saved ∗
   nextResultPointer args ↦ₘ? 16 ∗
   ⌜nextUint64PostFacts params x1 x2 x8 x9 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 inputBytes decoded saved /\
     x19 = Z_to_bv 64 (nextInputPointer args) /\
     sliceBytes = nextUint64SliceImage (nextInputPointer args) (Z.of_nat (length (nextInputBytes args))) /\
     nextUint64AcceptedBytes args decoded /\
     bv_unsigned x13 = nextUint64DecodedLength decoded /\
     x10 = Z_to_bv 64 8⌝ ∗ True)%I) := @PreOrder_Reflexive _ _ bi.entails_po _.
