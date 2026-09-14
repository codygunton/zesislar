Require Import ZesuSsz.Automation.All.
Require Import ZesuMachineMap.Machine.
Require Import ZesuSsz.Automation.MemoryWords.
Require Import ZesuSsz.Automation.Alignment.
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Export.Snapshots.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessByteLists.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessObservation.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessOutputSemantic.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessExactEncoderBytes.
From IslaTraces.write_success_05 Require Import instrs.
Import ZesuSsz.Automation.Calls.FramedContinuations.


Fixpoint byteListItemPayloadEvents (sp : bv 64) (items : list ByteListItem)
    (tail : spec) : spec :=
  match items with
  | [] => tail
  | item :: rest =>
      writeOutputEvents (sp - BV 64 48)%bv (BV 64 8)
        (writeSuccessPrivateBytes
          (writeSuccessEncodeU64 (bv_unsigned (byteListSize item))))
        (writeOutputEvents (byteListData item) (byteListSize item)
          (byteListBytes item) (byteListItemPayloadEvents sp rest tail))
  end.

Definition byteListsExactLoopFrame `{!islaG Sigma} `{!threadG}
    (P : iProp Sigma) (sp savedRa savedS0 savedS1 pointer : bv 64)
    (itemBase : Z) (done : list ByteListItem) (item : ByteListItem)
    (rest : list ByteListItem) (tail : spec) : iProp Sigma :=
  (reg_col byteListsLoopOtherRegShapes ∗
    "x1" ↦ᵣ: (fun value => ⌜valu_has_shape value (BitsShape 64)⌝) ∗
    "x2" ↦ᵣ RVal_Bits sp ∗
    "x5" ↦ᵣ: (fun value => ⌜valu_has_shape value (BitsShape 64)⌝) ∗
    "x6" ↦ᵣ: (fun value => ⌜valu_has_shape value (BitsShape 64)⌝) ∗
    "x9" ↦ᵣ RVal_Bits (pointer + BV 64 8)%bv ∗
    "x10" ↦ᵣ: (fun value => ⌜valu_has_shape value (BitsShape 64)⌝) ∗
    "x11" ↦ᵣ: (fun value => ⌜valu_has_shape value (BitsShape 64)⌝) ∗
    (bv_unsigned sp - 48) ↦ₘ? 48 ∗
    (bv_unsigned sp + 24) ↦ₘ savedRa ∗
    (bv_unsigned sp + 16) ↦ₘ savedS0 ∗
    (bv_unsigned sp + 8) ↦ₘ savedS1 ∗
    byteListProcessedResources itemBase done ∗
    byteListItemResources (bv_unsigned pointer) (item :: rest) ∗
    mmio_range (machineOutputAddress defaultMap) 16 ∗
    spec_trace (byteListItemPayloadEvents sp (item :: rest) tail) ∗
    ⌜S (length rest) < 2 ^ 64⌝ ∗
    ⌜bv_unsigned pointer =
      (itemBase + 16 * Z.of_nat (length done))%Z⌝ ∗
    ⌜bv_extract 0 3 pointer = BV 3 0⌝ ∗
    ⌜(mapRamBase defaultMap) <= bv_unsigned pointer⌝ ∗
    ⌜bv_unsigned pointer + 16 * Z.of_nat (S (length rest)) < (machineRamEnd defaultMap)⌝ ∗
    ⌜bv_extract 0 4 sp = BV 4 0⌝ ∗
    ⌜(mapRamBase defaultMap) <= bv_unsigned sp - 48⌝ ∗
    ⌜bv_unsigned sp < (machineRamEnd defaultMap)⌝ ∗
    P ∗
    instr_pre 0x15c58
      (byteListsLoopExit sp savedRa savedS0 savedS1
        (byteListEndPointer pointer (item :: rest)) itemBase
        (done ++ item :: rest) tail P) ∗
    True)%I.

Global Instance : LithiumUnfold (@byteListsExactLoopFrame) := I.

Definition byteListsExactLoopSpec `{!islaG Sigma} `{!threadG}
    (P : iProp Sigma) : iProp Sigma :=
  (∃ (sp savedRa savedS0 savedS1 pointer : bv 64) (itemBase : Z)
      (done : list ByteListItem) (item : ByteListItem)
      (rest : list ByteListItem) (tail : spec),
    reg_col zesu_ram_sys_regs ∗
    "x8" ↦ᵣ RVal_Bits (Z_to_bv 64 (Z.of_nat (S (length rest)))) ∗
    byteListsExactLoopFrame P sp savedRa savedS0 savedS1 pointer itemBase
      done item rest tail)%I.

Global Instance : LithiumUnfold (@byteListsExactLoopSpec) := I.

Definition byteListsExactAfterCallSpec `{!islaG Sigma} `{!threadG}
    (P : iProp Sigma) : iProp Sigma :=
  (∃ (sp savedRa savedS0 savedS1 pointer : bv 64) (itemBase : Z)
      (done : list ByteListItem) (item : ByteListItem)
      (rest : list ByteListItem) (tail : spec),
    reg_col zesu_ram_sys_regs ∗ reg_col byteListsLoopOtherRegShapes ∗
    "x1" ↦ᵣ RVal_Bits (BV 64 0x15c4c) ∗
    "x2" ↦ᵣ RVal_Bits sp ∗
    "x5" ↦ᵣ RVal_Bits (BV 64 (mapIoContextAddress defaultMap)) ∗
    "x6" ↦ᵣ: (fun value => ⌜valu_has_shape value (BitsShape 64)⌝) ∗
    "x8" ↦ᵣ RVal_Bits (Z_to_bv 64 (Z.of_nat (S (length rest)))) ∗
    "x9" ↦ᵣ RVal_Bits (pointer + BV 64 8)%bv ∗
    "x10" ↦ᵣ RVal_Bits (byteListData item) ∗
    "x11" ↦ᵣ RVal_Bits (byteListSize item) ∗
    (bv_unsigned sp - 48) ↦ₘ? 48 ∗
    (bv_unsigned sp + 24) ↦ₘ savedRa ∗
    (bv_unsigned sp + 16) ↦ₘ savedS0 ∗
    (bv_unsigned sp + 8) ↦ₘ savedS1 ∗
    byteListProcessedResources itemBase done ∗
    bv_unsigned pointer ↦ₘ byteListData item ∗
    (bv_unsigned pointer + 8) ↦ₘ byteListSize item ∗
    bv_unsigned (byteListData item) ↦ₘ∗ byteListBytes item ∗
    ⌜bv_unsigned (byteListSize item) = length (byteListBytes item)⌝ ∗
    byteListItemResources (bv_unsigned pointer + 16) rest ∗
    mmio_range (machineOutputAddress defaultMap) 16 ∗
    spec_trace (byteListItemPayloadEvents sp rest tail) ∗ P ∗
    ⌜S (length rest) < 2 ^ 64⌝ ∗
    ⌜bv_unsigned pointer =
      (itemBase + 16 * Z.of_nat (length done))%Z⌝ ∗
    ⌜bv_extract 0 3 pointer = BV 3 0⌝ ∗
    ⌜(mapRamBase defaultMap) <= bv_unsigned pointer⌝ ∗
    ⌜bv_unsigned pointer + 16 * Z.of_nat (S (length rest)) < (machineRamEnd defaultMap)⌝ ∗
    ⌜bv_extract 0 4 sp = BV 4 0⌝ ∗
    ⌜(mapRamBase defaultMap) <= bv_unsigned sp - 48⌝ ∗
    ⌜bv_unsigned sp < (machineRamEnd defaultMap)⌝ ∗
    □ instr_pre 0x15c3c (byteListsExactLoopSpec P) ∗
    instr_pre 0x15c58
      (byteListsLoopExit sp savedRa savedS0 savedS1
        (byteListEndPointer pointer (item :: rest)) itemBase
        (done ++ item :: rest) tail P) ∗
    True)%I.

Global Instance : LithiumUnfold (@byteListsExactAfterCallSpec) := I.

Definition byteListsExactEncoderFrame `{!islaG Sigma} `{!threadG}
    (P : iProp Sigma) (sp savedRa savedS0 savedS1 pointer : bv 64)
    (itemBase : Z) (done : list ByteListItem) (item : ByteListItem)
    (rest : list ByteListItem) (tail : spec) : iProp Sigma :=
  (reg_col byteListsLoopOtherRegShapes ∗
   (bv_unsigned sp + 24) ↦ₘ savedRa ∗
   (bv_unsigned sp + 16) ↦ₘ savedS0 ∗
   (bv_unsigned sp + 8) ↦ₘ savedS1 ∗
   byteListProcessedResources itemBase done ∗
   bv_unsigned pointer ↦ₘ byteListData item ∗
   (bv_unsigned pointer + 8) ↦ₘ byteListSize item ∗
   byteListItemResources (bv_unsigned pointer + 16) rest ∗
   ⌜bv_unsigned (byteListSize item) = length (byteListBytes item)⌝ ∗
   ⌜S (length rest) < 2 ^ 64⌝ ∗
   ⌜bv_unsigned pointer = (itemBase + 16 * Z.of_nat (length done))%Z⌝ ∗
   ⌜bv_extract 0 3 pointer = BV 3 0⌝ ∗
   ⌜(mapRamBase defaultMap) <= bv_unsigned pointer⌝ ∗
   ⌜bv_unsigned pointer + 16 * Z.of_nat (S (length rest)) < (machineRamEnd defaultMap)⌝ ∗
   ⌜bv_extract 0 4 sp = BV 4 0⌝ ∗
   ⌜(mapRamBase defaultMap) <= bv_unsigned sp - 48⌝ ∗
   ⌜bv_unsigned sp < (machineRamEnd defaultMap)⌝ ∗ P ∗
   instr_pre 0x15c58
     (byteListsLoopExit sp savedRa savedS0 savedS1
       (byteListEndPointer pointer (item :: rest)) itemBase
       (done ++ item :: rest) tail P) ∗ True)%I.
Global Instance : LithiumUnfold (@byteListsExactEncoderFrame) := I.

Definition encoderByteListsExactCallSpec `{!islaG Sigma} `{!threadG} :
    iProp Sigma :=
  (zesu_c_call 80
    (fun args sp RET =>
      ∃ (items : list ByteListItem) (tail : spec),
      byteListItemResources (bv_unsigned (args !!! 0%nat)) items ∗
      mmio_range (machineOutputAddress defaultMap) 16 ∗
      spec_trace
        (writeOutputEvents (sp - BV 64 48)%bv (BV 64 8)
          (writeSuccessPrivateBytes
            (writeSuccessEncodeU64 (Z.of_nat (length items))))
          (byteListItemPayloadEvents (sp - BV 64 32)%bv items tail)) ∗
      ⌜bv_unsigned (args !!! 1%nat) = length items⌝ ∗
      ⌜length items < 2 ^ 64⌝ ∗
      ⌜bv_extract 0 3 (args !!! 0%nat) = BV 3 0⌝ ∗
      ⌜(mapRamBase defaultMap) <= bv_unsigned (args !!! 0%nat)⌝ ∗
      ⌜bv_unsigned (args !!! 0%nat) + 16 * Z.of_nat (length items) <
        (machineRamEnd defaultMap)⌝ ∗
      ⌜bv_extract 0 4 sp = BV 4 0⌝ ∗
      ⌜(mapRamBase defaultMap) <= bv_unsigned sp - 80⌝ ∗
      ⌜bv_unsigned sp < (machineRamEnd defaultMap)⌝ ∗
      RET (fun _ =>
        byteListItemResources (bv_unsigned (args !!! 0%nat)) items ∗
        mmio_range (machineOutputAddress defaultMap) 16 ∗ spec_trace tail ∗ True)))%I.
Global Instance : LithiumUnfold (@encoderByteListsExactCallSpec) := I.

