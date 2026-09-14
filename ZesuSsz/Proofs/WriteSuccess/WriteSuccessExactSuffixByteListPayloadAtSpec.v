Require Import ZesuSsz.Automation.All.
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Export.Snapshots.
From iris.proofmode Require Import environments.
From IslaTraces.write_success_blocks Require Import Index.
From ZesuSsz.Proofs.WriteSuccess Require Import
  WriteSuccessNativeCode WriteSuccessExactPrefixCalls
  WriteSuccessByteLists WriteSuccessExactByteLists WriteSuccessExactByteListsSpec
  WriteSuccessObservation WriteSuccessOutputSemantic.
Import ListNotations.
Open Scope Z_scope.
Definition exactSuffixByteListAtOtherShapes : list (reg_kind * valu_shape) :=
  (fun register => (KindReg register, BitsShape 64)) <$>
  ["x5"; "x6"; "x7"; "x12"; "x13"; "x14"; "x15"; "x16"; "x17";
   "x28"; "x29"; "x30"; "x31"].
Definition exactSuffixByteListEntryAt `{!islaG Sigma} `{!threadG}
    (callPc sp pointer count : bv 64) (items : list ByteListItem) (tail : spec)
    (s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : bv 64) (Q : iProp Sigma) : iProp Sigma :=
  (    reg_col zesu_ram_sys_regs ∗ reg_col exactSuffixByteListAtOtherShapes ∗
    "x1" ↦ᵣ RVal_Bits callPc ∗ "x2" ↦ᵣ RVal_Bits sp ∗
    "x8" ↦ᵣ RVal_Bits s0 ∗
    "x9" ↦ᵣ RVal_Bits s1 ∗
    "x18" ↦ᵣ RVal_Bits s2 ∗
    "x19" ↦ᵣ RVal_Bits s3 ∗
    "x20" ↦ᵣ RVal_Bits s4 ∗
    "x21" ↦ᵣ RVal_Bits s5 ∗
    "x22" ↦ᵣ RVal_Bits s6 ∗
    "x23" ↦ᵣ RVal_Bits s7 ∗
    "x24" ↦ᵣ RVal_Bits s8 ∗
    "x25" ↦ᵣ RVal_Bits s9 ∗
    "x26" ↦ᵣ RVal_Bits s10 ∗
    "x27" ↦ᵣ RVal_Bits s11 ∗
    "x10" ↦ᵣ RVal_Bits pointer ∗ "x11" ↦ᵣ RVal_Bits count ∗
    (bv_unsigned sp - 80) ↦ₘ? 80 ∗
    byteListItemResources (bv_unsigned pointer) items ∗
    mmio_range (machineOutputAddress defaultMap) 16 ∗
    spec_trace (writeOutputEvents (sp - BV 64 48)%bv (BV 64 8)
      (writeSuccessPrivateBytes (writeSuccessEncodeU64 (Z.of_nat (length items))))
      (byteListItemPayloadEvents (sp - BV 64 32)%bv items tail)) ∗
    ⌜bv_unsigned count = Z.of_nat (length items)⌝ ∗
    ⌜length items < 2 ^ 64⌝ ∗
    ⌜bv_extract 0 3 pointer = BV 3 0⌝ ∗
    ⌜mapRamBase defaultMap <= bv_unsigned pointer⌝ ∗
    ⌜bv_unsigned pointer + 16 * Z.of_nat (length items) < machineRamEnd defaultMap⌝ ∗
    ⌜bv_unsigned sp `mod` 16 = 0⌝ ∗
    ⌜mapRamBase defaultMap <= bv_unsigned sp - 80 /\
      bv_unsigned sp < machineRamEnd defaultMap⌝ ∗ Q)%I.
Global Instance : LithiumUnfold (@exactSuffixByteListEntryAt) := I.
Definition exactSuffixByteListReturnAt `{!islaG Sigma} `{!threadG}
    (returnPc sp pointer count : bv 64) (items : list ByteListItem) (tail : spec)
    (s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : bv 64) (Q : iProp Sigma) : iProp Sigma :=
  (zesu_c_call_ret 80 [RVal_Bits s0; RVal_Bits s1; RVal_Bits s2; RVal_Bits s3; RVal_Bits s4; RVal_Bits s5; RVal_Bits s6; RVal_Bits s7; RVal_Bits s8; RVal_Bits s9; RVal_Bits s10; RVal_Bits s11] returnPc sp (fun _ =>
    byteListItemResources (bv_unsigned pointer) items ∗
    mmio_range (machineOutputAddress defaultMap) 16 ∗ spec_trace tail ∗ True) ∗ Q)%I.
Global Instance : LithiumUnfold (@exactSuffixByteListReturnAt) := I.
