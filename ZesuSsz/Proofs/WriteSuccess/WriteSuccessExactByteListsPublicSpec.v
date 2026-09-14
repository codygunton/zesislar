Require Import ZesuSsz.Automation.All.
Require Import ZesuMachineMap.Machine.
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessByteLists.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessExactByteListsSpec.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessExactByteListsDispatchSpec.

Definition byteListsExactPublicCountReturnSpec `{!islaG Sigma} `{!threadG} :
    iProp Sigma :=
  (∃ (callerSp ret savedS0 savedS1 pointer : bv 64)
      (saved : list valu) (items : list ByteListItem) (tail : spec),
    reg_col zesu_ram_sys_regs ∗
    "x8" ↦ᵣ RVal_Bits (Z_to_bv 64 (Z.of_nat (length items))) ∗
    byteListsExactDispatchFrame
      (byteListsPublicFrame callerSp ret savedS0 savedS1 saved
        (bv_unsigned pointer) items tail)
      (callerSp - BV 64 32)%bv ret savedS0 savedS1 pointer pointer
      (bv_unsigned pointer) [] items tail ∗
    ⌜length saved = 10%nat⌝ ∗
    ⌜bv_extract 0 4 callerSp = BV 4 0⌝ ∗
    ⌜(mapRamBase defaultMap) <= bv_unsigned callerSp - 80⌝ ∗
    ⌜bv_unsigned callerSp < (machineRamEnd defaultMap)⌝ ∗
    ⌜bv_extract 0 1 ret = BV 1 0⌝ ∗
    ⌜bv_extract 0 2 ret = BV 2 0⌝ ∗ True)%I.
Global Instance : LithiumUnfold (@byteListsExactPublicCountReturnSpec) := I.
