Require Import ZesuSsz.Automation.All.
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessByteLists.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessExactByteListsSpec.

Definition byteListsExactDispatchFrame `{!islaG Sigma} `{!threadG}
    (P : iProp Sigma) (sp savedRa savedS0 savedS1 pointer pointerRegister : bv 64)
    (itemBase : Z) (done : list ByteListItem) (items : list ByteListItem) (tail : spec) : iProp Sigma :=
  (reg_col byteListsLoopOtherRegShapes ∗
    "x1" ↦ᵣ: (fun value => ⌜valu_has_shape value (BitsShape 64)⌝) ∗
    "x2" ↦ᵣ RVal_Bits sp ∗
    "x5" ↦ᵣ: (fun value => ⌜valu_has_shape value (BitsShape 64)⌝) ∗
    "x6" ↦ᵣ: (fun value => ⌜valu_has_shape value (BitsShape 64)⌝) ∗
    "x9" ↦ᵣ RVal_Bits pointerRegister ∗
    "x10" ↦ᵣ: (fun value => ⌜valu_has_shape value (BitsShape 64)⌝) ∗
    "x11" ↦ᵣ: (fun value => ⌜valu_has_shape value (BitsShape 64)⌝) ∗
    (bv_unsigned sp - 48) ↦ₘ? 48 ∗
    (bv_unsigned sp + 24) ↦ₘ savedRa ∗
    (bv_unsigned sp + 16) ↦ₘ savedS0 ∗
    (bv_unsigned sp + 8) ↦ₘ savedS1 ∗
    byteListProcessedResources itemBase done ∗
    byteListItemResources (bv_unsigned pointer) items ∗
    mmio_range 0x2401a0c0 16 ∗
    spec_trace (byteListItemPayloadEvents sp items tail) ∗
    ⌜length items < 2 ^ 64⌝ ∗
    ⌜bv_unsigned pointer =
      (itemBase + 16 * Z.of_nat (length done))%Z⌝ ∗
    ⌜bv_extract 0 3 pointer = BV 3 0⌝ ∗
    ⌜0x20000000 <= bv_unsigned pointer⌝ ∗
    ⌜bv_unsigned pointer + 16 * Z.of_nat (length items) < 0x40000000⌝ ∗
    ⌜bv_extract 0 4 sp = BV 4 0⌝ ∗
    ⌜0x20000000 <= bv_unsigned sp - 48⌝ ∗
    ⌜bv_unsigned sp < 0x40000000⌝ ∗
    P ∗
    instr_pre 0x15c58
      (byteListsLoopExit sp savedRa savedS0 savedS1
        (byteListEndPointer pointer items) itemBase
        (done ++ items) tail P) ∗
    True)%I.

Global Instance : LithiumUnfold (@byteListsExactDispatchFrame) := I.

Definition byteListsExactDispatchSpec `{!islaG Sigma} `{!threadG}
    (P : iProp Sigma) : iProp Sigma :=
  (∃ (sp savedRa savedS0 savedS1 pointer : bv 64) (itemBase : Z)
      (done items : list ByteListItem) (tail : spec),
    reg_col zesu_ram_sys_regs ∗
    "x8" ↦ᵣ RVal_Bits (Z_to_bv 64 (Z.of_nat (length items))) ∗
    byteListsExactDispatchFrame P sp savedRa savedS0 savedS1 pointer
      (pointer + BV 64 8)%bv itemBase done items tail)%I.
Global Instance : LithiumUnfold (@byteListsExactDispatchSpec) := I.
