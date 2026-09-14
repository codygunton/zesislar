Require Import ZesuSsz.Automation.All.
Require Import ZesuMachineMap.Machine.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessExactByteListsPublicResources.
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Automation.Resources.
Require Import ZesuSsz.Automation.Alignment.
Require Import ZesuSsz.Automation.ByteListResources.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessByteLists.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessExactByteListsSpec.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessExactByteListsPublicSpec.

Lemma byte_lists_public_count_resources `{!islaG Sigma} `{!threadG}
    (sp ret s0 s1 pointer count b12 b13 b14 b15 b16 b17 : bv 64)
    (saved : list valu) (items : list ByteListItem) (tail : spec) :
  length saved = 10%nat ->
  bv_extract 0 4 sp = BV 4 0 ->
  (mapRamBase defaultMap) <= bv_unsigned sp - 80 ->
  bv_unsigned sp < (machineRamEnd defaultMap) ->
  bv_extract 0 1 ret = BV 1 0 ->
  bv_extract 0 2 ret = BV 2 0 ->
  bv_unsigned count = Z.of_nat (length items) ->
  length items < 2 ^ 64 ->
  bv_extract 0 3 pointer = BV 3 0 ->
  (mapRamBase defaultMap) <= bv_unsigned pointer ->
  bv_unsigned pointer + 16 * Z.of_nat (length items) < (machineRamEnd defaultMap) ->
  □ instr_pre 0x15c58
    (byteListsLoopExit (sp - BV 64 32)%bv ret s0 s1
      (byteListEndPointer pointer items) (bv_unsigned pointer) items tail
      (byteListsPublicFrame sp ret s0 s1 saved (bv_unsigned pointer) items tail)) -∗
  (reg_col zesu_ram_sys_regs ∗
   reg_col [(KindReg "x6", BitsShape 64); (KindReg "x7", BitsShape 64);
     (KindReg "x28", BitsShape 64); (KindReg "x29", BitsShape 64);
     (KindReg "x30", BitsShape 64); (KindReg "x31", BitsShape 64)] ∗
   "x12" ↦ᵣ RVal_Bits b12 ∗ "x13" ↦ᵣ RVal_Bits b13 ∗
   "x14" ↦ᵣ RVal_Bits b14 ∗ "x15" ↦ᵣ RVal_Bits b15 ∗
   "x16" ↦ᵣ RVal_Bits b16 ∗ "x17" ↦ᵣ RVal_Bits b17 ∗
   "x1" ↦ᵣ RVal_Bits (BV 64 0x15c34) ∗
   "x2" ↦ᵣ RVal_Bits (sp - BV 64 32)%bv ∗
   "x5" ↦ᵣ RVal_Bits (BV 64 (mapIoContextAddress defaultMap)) ∗
   "x8" ↦ᵣ RVal_Bits count ∗ "x9" ↦ᵣ RVal_Bits pointer ∗
   "x10" ↦ᵣ RVal_Bits (sp - (BV 64 32 + BV 64 16))%bv ∗
   "x11" ↦ᵣ RVal_Bits (BV 64 8) ∗
   (bv_unsigned sp - 80) ↦ₘ? 32 ∗
   (bv_unsigned (sp - BV 64 32)%bv - 16) ↦ₘ? 16 ∗
   bv_unsigned (sp + BV 64 18446744073709551584 + BV 64 24)%bv ↦ₘ ret ∗
   bv_unsigned (sp + BV 64 18446744073709551584 + BV 64 16)%bv ↦ₘ s0 ∗
   bv_unsigned (sp + BV 64 18446744073709551584 + BV 64 8)%bv ↦ₘ s1 ∗
   byteListItemResources (bv_unsigned pointer) items ∗
   mmio_range (machineOutputAddress defaultMap) 16 ∗
   spec_trace (byteListItemPayloadEvents (sp - BV 64 32)%bv items tail) ∗
   byteListsPublicFrame sp ret s0 s1 saved (bv_unsigned pointer) items tail ∗ True) -∗
  byteListsExactPublicCountReturnSpec.
Proof.
  apply byte_lists_public_count_resources_checked.
Qed.
Print Assumptions byte_lists_public_count_resources.
