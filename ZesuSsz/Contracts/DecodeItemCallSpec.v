Require Import ZesuSsz.Automation.All.
From Coq Require Import List ZArith.
From stdpp Require Import base list bitvector.definitions.
Require Import isla.riscv64.riscv64.
Require Import EvmSailRlp.evm_rlp_types.
Require Import ZesuMachineMap.Machine.
Require Import ZesuSsz.Contracts.RlpDecodeItem.
Require Import ZesuSsz.Contracts.RlpDecodeItemContract.
Require Import ZesuSsz.Automation.Calls.
Require Import ZesuSsz.Contracts.DecodeItemCompositional.
Require Import ZesuSsz.Contracts.DecodeItemSelected.
Require Import ZesuSsz.Contracts.Level1.
Import ListNotations.
Open Scope Z_scope.
Open Scope stdpp_scope.

(* The call convention owns static machine registers. The data predicate
   owns both dynamic registers and returns their required shapes. *)
Definition decodeItemCallMap : MachineMap :=
  {| mapPopulatedSections := mapPopulatedSections defaultMap;
     mapRamBase := mapRamBase defaultMap;
     mapRamSize := mapRamSize defaultMap;
     mapTextBase := mapTextBase defaultMap;
     mapTextEnd := mapTextEnd defaultMap;
     mapRodataBase := mapRodataBase defaultMap;
     mapRodataEnd := mapRodataEnd defaultMap;
     mapDataBase := mapDataBase defaultMap;
     mapHeapBase := mapHeapBase defaultMap;
     mapHeapEnd := mapHeapEnd defaultMap;
     mapInputBufferAddress := mapInputBufferAddress defaultMap;
     mapInputCapacity := mapInputCapacity defaultMap;
     mapIoContextAddress := mapIoContextAddress defaultMap;
     mapStartPc := mapStartPc defaultMap;
     mapReadInputPc := mapReadInputPc defaultMap;
     mapWriteOutputPc := mapWriteOutputPc defaultMap;
     mapZkvmExitPc := mapZkvmExitPc defaultMap;
     mapMemcpyPc := mapMemcpyPc defaultMap;
     mapMainPc := mapMainPc defaultMap;
     mapHeapTopAddress := mapHeapTopAddress defaultMap;
     mapHeapPosAddress := mapHeapPosAddress defaultMap;
     mapRomBase := mapRomBase defaultMap;
     mapRomSize := mapRomSize defaultMap;
     mapClintBase := mapClintBase defaultMap;
     mapClintSize := mapClintSize defaultMap;
     mapHtifTohost := mapHtifTohost defaultMap;
     mapEnableWritableMisa := mapEnableWritableMisa defaultMap;
     mapEnableRvc := mapEnableRvc defaultMap;
     mapEnableFdext := mapEnableFdext defaultMap;
     mapEnablePmp := mapEnablePmp defaultMap;
     mapEnableDirtyUpdate := mapEnableDirtyUpdate defaultMap;
     mapEnableMisalignedAccess := mapEnableMisalignedAccess defaultMap;
     mapMtvalHasIllegalInstBits := mapMtvalHasIllegalInstBits defaultMap;
     mapInsnsPerTick := mapInsnsPerTick defaultMap;
     mapZiskPlatform := false;
     mapPrivilege := mapPrivilege defaultMap;
     mapMisa := mapMisa defaultMap;
     mapMtvec := mapMtvec defaultMap;
     mapMstatusMask := mapMstatusMask defaultMap;
     mapMstatusValue := mapMstatusValue defaultMap |}.

Definition decodeItemCallDataArgs
    (argv : list (bv 64)) (sp : bv 64) (inputEnd : Z)
    (input before : list byte) : DecodeItemArgs :=
  {| decodeItemOutputPointer := bv_unsigned (argv !!! 0%nat);
     decodeItemInputPointer := bv_unsigned (argv !!! 1%nat);
     decodeItemInputLength := bv_unsigned (argv !!! 2%nat);
     decodeItemInputBytes := input;
     decodeItemBeforeStorage := before;
     decodeItemStackPointer := bv_unsigned sp;
     decodeItemReturnAddress := 0;
     decodeItemSavedFramePointer := Z_to_bv 64 0;
     decodeItemInputEnd := inputEnd |}.

Definition decodeItemCallSpec `{!islaG Sigma} `{!threadG} : iProp Sigma :=
  (machine_call decodeItemCallMap decodeItemStackBytes
    (fun argv sp RET =>
      ∃ (input before : list byte) (inputEndBits : bv 64),
      "zisk_input_end" ↦ᵣ RVal_Bits inputEndBits ∗
      reg_col [(KindReg "zisk_free_input", BitsShape 64)] ∗
      bv_unsigned (argv !!! 1%nat) ↦ₘ∗ input ∗
      bv_unsigned (argv !!! 0%nat) ↦ₘ∗ before ∗
      ⌜decodeItemC1BDomain
          (decodeItemCallDataArgs argv sp (bv_unsigned inputEndBits) input before)⌝ ∗
      RET (fun _ =>
        ∃ after : DecodeItemOutcome,
        "zisk_input_end" ↦ᵣ RVal_Bits inputEndBits ∗
        reg_col [(KindReg "zisk_free_input", BitsShape 64)] ∗
        bv_unsigned (argv !!! 1%nat) ↦ₘ∗ input ∗
        bv_unsigned (argv !!! 0%nat) ↦ₘ∗ after ∗
        ⌜DecodeMeaningModuloKnownBugs
            (decodeItemCallDataArgs argv sp (bv_unsigned inputEndBits) input before) after⌝ ∗
        True)))%I.
Global Instance : LithiumUnfold (@decodeItemCallSpec) := I.
Global Typeclasses Opaque decodeItemCallSpec.
