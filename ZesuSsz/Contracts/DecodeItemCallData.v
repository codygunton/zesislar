From Coq Require Import List ZArith.
From stdpp Require Import base list bitvector.definitions.
Require Import EvmSailRlp.evm_rlp_types.
Require Import ZesuMachineMap.Machine.
Require Import ZesuSsz.Contracts.RlpDecodeItem.
Require Import ZesuSsz.Contracts.RlpDecodeItemContract.
Import ListNotations.
Open Scope Z_scope.
Open Scope stdpp_scope.

(* Core-free call data of the decodeItem call specs. DecodeItemCallSpec.v
   (frozen core) and DecodeItemCallSpec2.v (Automation2) share them. *)
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
