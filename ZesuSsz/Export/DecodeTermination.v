Require Import ZesuSsz.Automation.All.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessValueBlock.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessOutputSemantic.
Require Import isla.riscv64.riscv64.
Require Import ZesuMachineMap.Machine.
Require Import ZesuSsz.Contracts.Endpoints.
Require Import ZesuSsz.Contracts.DecodeHeap.
Require Import ZesuSsz.Contracts.DecodeMachine.
Require Import ZesuSsz.Proofs.ReadInput.ReadInput.
Require Import ZesuSsz.Proofs.WriteFailure.WriteFailure.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessNativeContract.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessObservation.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessPrologueSpec.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessTransactionsSpec.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessAccessListsSpec.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessByteLists.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessPostTransactionResources.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessPostTransactionDescriptors.
Require Import ZesuSsz.Export.TerminationResources.

Definition physicalMemoryBacked (sigma : seq_global_state) (address size : Z) : Prop :=
  forall offset, 0 <= offset < size ->
    exists byte : bv 8,
      (Z_to_bv_checked 64 (address + offset) ≫= (fun pointer => seq_mem sigma !! pointer)) = Some byte.
Definition physicalMmioRange (sigma : seq_global_state) (address size : Z) : Prop :=
  forall offset, 0 <= offset < size ->
    (Z_to_bv_checked 64 (address + offset) ≫= (fun pointer => seq_mem sigma !! pointer)) = None.
Definition physicalRegisterShapes (regs : reg_map)
    (shapes : list (reg_kind * valu_shape)) : Prop :=
  Forall (fun shape => exists register value,
    shape.1 = KindReg register /\ regs !! register = Some value /\
    valu_has_shape value shape.2) shapes.
Definition physicalInstructionBoundary (pc : Z)
    (theta : seq_local_state) (sigma : seq_global_state) : Prop :=
  seq_pc_reg theta = "PC" /\ seq_nb_state theta = false /\
  physicalRegister64 (seq_regs theta) "PC" (Z_to_bv 64 pc) /\
  seq_instrs sigma !! Z_to_bv 64 pc = Some (seq_trace theta).
Definition physicalDecoderEntryBoundary (pc : Z)
    (theta : seq_local_state) : Prop :=
  seq_pc_reg theta = "PC" /\ seq_nb_state theta = false /\
  physicalRegister64 (seq_regs theta) "PC" (Z_to_bv 64 pc).
Definition physicalNativeStaticMemory (sigma : seq_global_state) : Prop :=
  physicalMemoryBytes sigma (mapRodataBase defaultMap + 0x7c5)
    (writeSuccessPrivateBytes [90; 83; 83; 90; 1; 1]).
Definition physicalMainPreservedMemory (args : DecodeBoundaryArgs)
    (sigma : seq_global_state) : Prop :=
  decodeInputAddress args = mapInputBufferAddress defaultMap /\
  decodeAllocatorStateAddress args = mainAllocatorStateAddress /\
  decodeAllocatorVtableAddress args = mainAllocatorVtableAddress /\
  Z.of_nat (length (decodeInput args)) <= mapInputCapacity defaultMap /\
  physicalMemoryBytes sigma (mapInputBufferAddress defaultMap)
    (readInputMemory (decodeInput args)) /\
  physicalMemoryValue sigma (mapIoContextAddress defaultMap)
    (Z_to_bv 64 (Z.of_nat (length (decodeInput args)))) /\
  physicalMemoryBytes sigma mainAllocatorVtableAddress mainAllocatorVtableBytes /\
  physicalMemoryBytes sigma mainFailurePayloadAddress failureMemory /\
  physicalMmioRange sigma (machineExitAddress defaultMap) 8.
Definition physicalMainHeapEntry (args : DecodeBoundaryArgs)
    (sigma : seq_global_state) : Prop :=
  physicalMemoryBacked sigma (mapHeapBase defaultMap)
    (mapHeapEnd defaultMap - mapHeapBase defaultMap) /\
  physicalMemoryValue sigma mainAllocatorStateAddress (BV 64 0) /\
  physicalMemoryValue sigma (mapHeapTopAddress defaultMap)
    (Z_to_bv 64 (mapHeapEnd defaultMap)) /\
  physicalMemoryValue sigma (mapHeapPosAddress defaultMap)
    (Z_to_bv 64 (mapHeapBase defaultMap)) /\
  physicalMemoryBacked sigma (decodeStackPointer args - 2048) 48 /\
  physicalMemoryBacked sigma (decodeStackPointer args - 2080) 32 /\
  physicalNativeStaticMemory sigma.
Definition physicalMainHeapFailureExit (args : DecodeBoundaryArgs)
    (sigma : seq_global_state) : Prop :=
  exists allocatorState heapTop heapPos : bv 64,
  physicalMemoryBacked sigma (mapHeapBase defaultMap)
    (mapHeapEnd defaultMap - mapHeapBase defaultMap) /\
  physicalMemoryValue sigma mainAllocatorStateAddress allocatorState /\
  physicalMemoryValue sigma (mapHeapTopAddress defaultMap) heapTop /\
  physicalMemoryValue sigma (mapHeapPosAddress defaultMap) heapPos /\
  physicalMemoryBacked sigma (decodeStackPointer args - 2048) 48 /\
  physicalMemoryBacked sigma (decodeStackPointer args - 2080) 32 /\
  physicalNativeStaticMemory sigma.
Definition physicalByteArray (sigma : seq_global_state)
    (pointer : bv 64) (bytes : list (bv 8)) : Prop :=
  match bytes with
  | [] => True
  | _ :: _ => physicalMemoryBytes sigma (bv_unsigned pointer) bytes /\
      mapRamBase defaultMap <= bv_unsigned pointer /\
      bv_unsigned pointer + Z.of_nat (length bytes) < machineRamEnd defaultMap
  end.
Definition physicalAccessEntry (sigma : seq_global_state)
    (entry : writeSuccessAccessEntry) : Prop :=
  writeSuccessAccessEntryValid entry /\
  match writeSuccessAccessEntryStorageCount entry with
  | O => True
  | S _ => physicalMemoryBytes sigma
      (bv_unsigned (writeSuccessAccessEntryStoragePointer entry))
      (writeSuccessAccessEntryStorageBytes entry) /\
      mapRamBase defaultMap <= bv_unsigned (writeSuccessAccessEntryStoragePointer entry) /\
      bv_unsigned (writeSuccessAccessEntryStoragePointer entry) +
        Z.of_nat (length (writeSuccessAccessEntryStorageBytes entry)) < machineRamEnd defaultMap
  end.
Definition physicalTransactionData (sigma : seq_global_state)
    (transaction : writeSuccessTransaction) : Prop :=
  writeSuccessTransactionValid transaction /\
  physicalByteArray sigma (writeSuccessTransactionDataPointer transaction)
    (writeSuccessTransactionData transaction) /\
  physicalByteArray sigma (writeSuccessTransactionAccessPointer transaction)
    (writeSuccessTransactionAccessBytes transaction) /\
  Forall (physicalAccessEntry sigma) (writeSuccessTransactionAccessEntries transaction) /\
  physicalByteArray sigma (writeSuccessTransactionBlobPointer transaction)
    (writeSuccessTransactionBlobBytes transaction) /\
  physicalByteArray sigma (writeSuccessTransactionAuthorizationPointer transaction)
    (writeSuccessTransactionAuthorizationBytes transaction).
Fixpoint physicalByteLists (sigma : seq_global_state) (address : Z)
    (items : list ByteListItem) : Prop :=
  match items with
  | [] => True
  | item :: rest =>
      physicalMemoryValue sigma address (byteListData item) /\
      physicalMemoryValue sigma (address + 8) (byteListSize item) /\
      physicalMemoryBytes sigma (bv_unsigned (byteListData item)) (byteListBytes item) /\
      bv_unsigned (byteListSize item) = Z.of_nat (length (byteListBytes item)) /\
      physicalByteLists sigma (address + 16) rest
  end.
Definition physicalDescriptor (sigma : seq_global_state)
    (descriptor : WriteOutputDescriptor) (bytes : list (bv 8)) : Prop :=
  physicalMemoryBytes sigma (bv_unsigned descriptor.1) bytes /\
  bv_unsigned descriptor.2 = Z.of_nat (length bytes).
Definition physicalOptionalDescriptor (sigma : seq_global_state)
    (descriptor : option WriteOutputDescriptor) (bytes : option (list (bv 8))) : Prop :=
  match descriptor, bytes with
  | None, None => True
  | Some value, Some payload => physicalDescriptor sigma value payload
  | _, _ => False
  end.

Definition physicalPostTransactionData (sigma : seq_global_state)
    (sp : bv 64) (sourceBytes decodedBytes : list (bv 8))
    (data : WriteSuccessPostTransactionData) : Prop :=
  let source := writeSuccessPostSourceWords sourceBytes in
  let tail := writeSuccessPostTailWords decodedBytes in
  physicalDescriptor sigma (writeSuccessPostBytes1571c data) (writeSuccessPostBytes1571cPayload data) /\
  physicalMemoryBytes sigma (bv_unsigned (writeSuccessPostWord source 74))
    (writeSuccessPostHashesPayload data) /\
  length (writeSuccessPostHashesPayload data) = (32 * writeSuccessPostHashesCount data)%nat /\
  physicalDescriptor sigma (writeSuccessPostBytes158e0 data) (writeSuccessPostBytes158e0Payload data) /\
  physicalDescriptor sigma (writeSuccessPostBytes158f0 data) (writeSuccessPostBytes158f0Payload data) /\
  physicalDescriptor sigma (writeSuccessPostBytes15900 data) (writeSuccessPostBytes15900Payload data) /\
  physicalDescriptor sigma (writeSuccessPostBytes15910 data) (writeSuccessPostBytes15910Payload data) /\
  physicalDescriptor sigma (writeSuccessPostBytes15920 data) (writeSuccessPostBytes15920Payload data) /\
  physicalByteLists sigma (bv_unsigned (writeSuccessPostWord tail 0)) (writeSuccessPostByteLists15930 data) /\
  physicalByteLists sigma (bv_unsigned (writeSuccessPostWord tail 2)) (writeSuccessPostByteLists15940 data) /\
  physicalByteLists sigma (bv_unsigned (writeSuccessPostWord tail 4)) (writeSuccessPostByteLists15950 data) /\
  physicalOptionalDescriptor sigma (writeSuccessPostConditional1596c data)
    (writeSuccessPostConditional1596cPayload data) /\
  physicalByteLists sigma (bv_unsigned (writeSuccessPostWord tail 14)) (writeSuccessPostByteLists159c8 data) /\
  writeSuccessPostTransactionDataFacts sp sourceBytes decodedBytes data.

Definition physicalNativeData (sigma : seq_global_state)
    (witness : writeSuccessNativeWitness WriteSuccessObservation) : Prop :=
  let frame := bv_unsigned (writeSuccessFrameSp witness) in
  physicalMemoryBacked sigma (frame - 48) 48 /\
  physicalMemoryBacked sigma (frame - 80) 32 /\
  physicalMemoryBytes sigma
    (bv_unsigned (writeSuccessValueWord (writeSuccessValues witness) 4)) (writeSuccessPayload witness) /\
  physicalMemoryBytes sigma (writeSuccessTransactionBase witness) (WriteSuccessNativeContract.writeSuccessTransactionBytes witness) /\
  Forall (physicalTransactionData sigma) (writeSuccessTransactions witness) /\
  length (WriteSuccessNativeContract.writeSuccessTransactionBytes witness) = (288 * length (writeSuccessTransactions witness))%nat /\
  (length (writeSuccessTransactions witness) < 2^64)%nat /\
  writeSuccessTransactionBase witness `mod` 8 = 0 /\
  mapRamBase defaultMap <= writeSuccessTransactionBase witness /\
  writeSuccessTransactionBase witness + Z.of_nat (length (WriteSuccessNativeContract.writeSuccessTransactionBytes witness)) < machineRamEnd defaultMap /\
  physicalByteLists sigma (bv_unsigned (writeSuccessValueWord (writeSuccessValues witness) 9))
    (writeSuccessRawTransactions witness) /\
  physicalMemoryBytes sigma (bv_unsigned (writeSuccessWithdrawalsBase witness)) (writeSuccessWithdrawalsBytes witness) /\
  physicalPostTransactionData sigma (writeSuccessFrameSp witness) (writeSuccessSourceBytes witness)
    (writeSuccessDecodedBytes witness) (writeSuccessPostData witness) /\
  physicalNativeStaticMemory sigma.

Definition physicalMainDecodeBounds (args : DecodeBoundaryArgs) : Prop :=
  decodeReturnAddress args = machinePc 0x4bdc /\
  length (decodeSavedRegisters args) = 12%nat /\
  decodeStackPointer args `mod` 16 = 0 /\
  mapRamBase defaultMap + 0x880 <= decodeStackPointer args /\
  decodeStackPointer args + 0x7d0 < machineRamEnd defaultMap.
Definition physicalMainDecodeFrame (args : DecodeBoundaryArgs)
    (sigma : seq_global_state) (allocatorPointer allocatorSize : bv 64) : Prop :=
  physicalCallerFrame sigma (Z_to_bv 64 (decodeStackPointer args))
    (Z_to_bv 64 (decodeInputAddress args))
    (Z_to_bv 64 (Z.of_nat (length (decodeInput args)))) allocatorPointer allocatorSize
    (Z_to_bv 64 (decodeSavedReturnAddress args)) (decodeFramePadding args) /\
  physicalMemoryBacked sigma (decodeStackPointer args - 104) 104 /\
  physicalMemoryBacked sigma (decodeStackPointer args - 0x7d0) 1896 /\
  physicalMmioRange sigma (machineOutputAddress defaultMap) 16 /\
  physicalMainPreservedMemory args sigma.
Definition physicalIntervalsSeparated (left right : Z * Z) : Prop :=
  left.2 = 0 \/ right.2 = 0 \/
  left.1 + left.2 <= right.1 \/ right.1 + right.2 <= left.1.
Fixpoint physicalFootprintSeparated (regions : list (Z * Z)) : Prop :=
  match regions with
  | [] => True
  | region :: rest => Forall (physicalIntervalsSeparated region) rest /\
      physicalFootprintSeparated rest
  end.
Definition physicalBytesRegion (address : Z) (bytes : list (bv 8)) : Z * Z :=
  (address, Z.of_nat (length bytes)).
Definition physicalMainCommonFootprint (args : DecodeBoundaryArgs) : list (Z * Z) :=
  [(decodeStackPointer args - 2080, 2976);
   physicalBytesRegion (mapInputBufferAddress defaultMap) (readInputMemory (decodeInput args));
   (mapIoContextAddress defaultMap, 8);
   physicalBytesRegion mainAllocatorVtableAddress mainAllocatorVtableBytes;
   physicalBytesRegion mainFailurePayloadAddress failureMemory;
   (mapRodataBase defaultMap + 0x7c5, 6)].
Definition physicalMainHeapFootprint : list (Z * Z) :=
  [(mapHeapBase defaultMap, mapHeapEnd defaultMap - mapHeapBase defaultMap);
   (mainAllocatorStateAddress, 8); (mapHeapTopAddress defaultMap, 8);
   (mapHeapPosAddress defaultMap, 8)].
Definition physicalAccessFootprint (entry : writeSuccessAccessEntry) : list (Z * Z) :=
  match writeSuccessAccessEntryStorageCount entry with
  | O => []
  | S _ => [physicalBytesRegion (bv_unsigned (writeSuccessAccessEntryStoragePointer entry))
      (writeSuccessAccessEntryStorageBytes entry)]
  end.
Definition physicalTransactionFootprint (transaction : writeSuccessTransaction) : list (Z * Z) :=
  [physicalBytesRegion (bv_unsigned (writeSuccessTransactionDataPointer transaction))
     (writeSuccessTransactionData transaction);
   physicalBytesRegion (bv_unsigned (writeSuccessTransactionAccessPointer transaction))
     (writeSuccessTransactionAccessBytes transaction);
   physicalBytesRegion (bv_unsigned (writeSuccessTransactionBlobPointer transaction))
     (writeSuccessTransactionBlobBytes transaction);
   physicalBytesRegion (bv_unsigned (writeSuccessTransactionAuthorizationPointer transaction))
     (writeSuccessTransactionAuthorizationBytes transaction)] ++
  List.concat (physicalAccessFootprint <$> writeSuccessTransactionAccessEntries transaction).
Definition physicalByteListsFootprint (address : Z) (items : list ByteListItem) : list (Z * Z) :=
  (address, 16 * Z.of_nat (length items)) ::
  ((fun item => physicalBytesRegion (bv_unsigned (byteListData item)) (byteListBytes item)) <$> items).
Definition physicalDescriptorRegion (descriptor : WriteOutputDescriptor)
    (bytes : list (bv 8)) : Z * Z := physicalBytesRegion (bv_unsigned descriptor.1) bytes.
Definition physicalPostFootprint (sourceBytes decodedBytes : list (bv 8))
    (data : WriteSuccessPostTransactionData) : list (Z * Z) :=
  let source := writeSuccessPostSourceWords sourceBytes in
  let tail := writeSuccessPostTailWords decodedBytes in
  [physicalDescriptorRegion (writeSuccessPostBytes1571c data) (writeSuccessPostBytes1571cPayload data);
   physicalBytesRegion (bv_unsigned (writeSuccessPostWord source 74)) (writeSuccessPostHashesPayload data);
   physicalDescriptorRegion (writeSuccessPostBytes158e0 data) (writeSuccessPostBytes158e0Payload data);
   physicalDescriptorRegion (writeSuccessPostBytes158f0 data) (writeSuccessPostBytes158f0Payload data);
   physicalDescriptorRegion (writeSuccessPostBytes15900 data) (writeSuccessPostBytes15900Payload data);
   physicalDescriptorRegion (writeSuccessPostBytes15910 data) (writeSuccessPostBytes15910Payload data);
   physicalDescriptorRegion (writeSuccessPostBytes15920 data) (writeSuccessPostBytes15920Payload data)] ++
  physicalByteListsFootprint (bv_unsigned (writeSuccessPostWord tail 0)) (writeSuccessPostByteLists15930 data) ++
  physicalByteListsFootprint (bv_unsigned (writeSuccessPostWord tail 2)) (writeSuccessPostByteLists15940 data) ++
  physicalByteListsFootprint (bv_unsigned (writeSuccessPostWord tail 4)) (writeSuccessPostByteLists15950 data) ++
  (match writeSuccessPostConditional1596c data, writeSuccessPostConditional1596cPayload data with
   | Some descriptor, Some bytes => [physicalDescriptorRegion descriptor bytes]
   | _, _ => [] end) ++
  physicalByteListsFootprint (bv_unsigned (writeSuccessPostWord tail 14)) (writeSuccessPostByteLists159c8 data).
Definition physicalNativeDynamicFootprint
    (witness : writeSuccessNativeWitness WriteSuccessObservation) : list (Z * Z) :=
  [physicalBytesRegion (bv_unsigned (writeSuccessValueWord (writeSuccessValues witness) 4))
     (writeSuccessPayload witness);
   physicalBytesRegion (writeSuccessTransactionBase witness) (WriteSuccessNativeContract.writeSuccessTransactionBytes witness);
   physicalBytesRegion (bv_unsigned (writeSuccessWithdrawalsBase witness)) (writeSuccessWithdrawalsBytes witness)] ++
  List.concat (physicalTransactionFootprint <$> writeSuccessTransactions witness) ++
  physicalByteListsFootprint (bv_unsigned (writeSuccessValueWord (writeSuccessValues witness) 9))
    (writeSuccessRawTransactions witness) ++
  physicalPostFootprint (writeSuccessSourceBytes witness) (writeSuccessDecodedBytes witness) (writeSuccessPostData witness).

Definition physicalMainDecodeObject (successExitTail : DecodeBoundaryArgs -> spec)
    (args : DecodeBoundaryArgs) (outcome : DecodeBoundaryOutcome WriteSuccessObservation)
    (sigma : seq_global_state) : Prop :=
  match outcome with
  | DecodeBoundarySuccess observation =>
      exists witness : writeSuccessNativeWitness WriteSuccessObservation,
      writeSuccessWitnessWellFormed
        {| successReturnAddress := machinePc 0x4bf0;
           successStackPointer := decodeStackPointer args;
           successDecodedAddress := decodeStackPointer args + 32;
           successDecoded := observation;
           successInputSize := length (decodeInput args) |} witness /\
      writeSuccessTraceTail witness = successExitTail args /\
      decodeSavedRegisters args =
        [writeSuccessSavedS0 witness; writeSuccessSavedS1 witness; writeSuccessSavedS2 witness;
         writeSuccessSavedS3 witness; writeSuccessSavedS4 witness; writeSuccessSavedS5 witness;
         writeSuccessSavedS6 witness; writeSuccessSavedS7 witness; writeSuccessSavedS8 witness;
         writeSuccessSavedS9 witness; writeSuccessSavedS10 witness; writeSuccessSavedS11 witness] /\
      physicalMemoryValue sigma (decodeStackPointer args + 880) (BV 16 0) /\
      physicalMemoryBytes sigma (bv_unsigned (writeSuccessDecodedPointer witness)) (writeSuccessDecodedBytes witness) /\
      physicalNativeData sigma witness /\
      physicalFootprintSeparated (physicalMainCommonFootprint args ++ physicalNativeDynamicFootprint witness)
  | DecodeBoundaryFailure =>
      exists (status : bv 16) (objectBytes : list (bv 8)),
      status <> BV 16 0 /\ length objectBytes = 848%nat /\
      physicalMemoryValue sigma (decodeStackPointer args + 880) status /\
      physicalMemoryBytes sigma (decodeStackPointer args + 32) objectBytes
  end.

Definition physicalMainDecodeEntry (program : gmap addr isla_trace)
    (decodeTail successExitTail : DecodeBoundaryArgs -> spec)
    (initial : spec) (prefix : list seq_label) (args : DecodeBoundaryArgs)
    (theta : seq_local_state) (sigma : seq_global_state) : Prop :=
  let sp := Z_to_bv 64 (decodeStackPointer args) in
  seq_instrs sigma = program /\ physicalDecoderEntryBoundary (machinePc 0x2048) theta /\
  physicalMainDecodeBounds args /\
  physicalFootprintSeparated (physicalMainCommonFootprint args ++ physicalMainHeapFootprint) /\
  physicalRegisterShapes (seq_regs theta) zesu_sys_regs /\
  physicalRegisterShapes (seq_regs theta)
    ((fun register => (KindReg register, BitsShape 64)) <$>
      List.filter (fun register => negb (String.eqb register "x13")) writeSuccessOtherRegisters) /\
  physicalRegister64 (seq_regs theta) "x1" (Z_to_bv 64 (machinePc 0x4bdc)) /\
  physicalRegister64 (seq_regs theta) "x2" sp /\
  physicalSavedRegisters (seq_regs theta) (decodeSavedRegisters args) /\
  physicalRegister64 (seq_regs theta) "x10" (sp + BV 64 32)%bv /\
  physicalRegister64 (seq_regs theta) "x11" (sp + BV 64 16)%bv /\
  physicalRegister64 (seq_regs theta) "x12" (Z_to_bv 64 (decodeInputAddress args)) /\
  physicalRegister64 (seq_regs theta) "x13" (Z_to_bv 64 (Z.of_nat (length (decodeInput args)))) /\
  physicalMainDecodeFrame args sigma (Z_to_bv 64 (decodeAllocatorStateAddress args))
    (Z_to_bv 64 (decodeAllocatorVtableAddress args)) /\
  physicalMemoryBacked sigma (decodeStackPointer args + 32) 848 /\
  physicalMemoryBacked sigma (decodeStackPointer args + 880) 2 /\
  physicalMainHeapEntry args sigma /\ traceResidual initial prefix (decodeTail args).
Definition physicalMainDecodeExit (program : gmap addr isla_trace)
    (decodeTail successExitTail : DecodeBoundaryArgs -> spec)
    (initial : spec) (prefix : list seq_label) (args : DecodeBoundaryArgs)
    (outcome : DecodeBoundaryOutcome WriteSuccessObservation)
    (theta : seq_local_state) (sigma : seq_global_state) : Prop :=
  let sp := Z_to_bv 64 (decodeStackPointer args) in
  seq_instrs sigma = program /\ physicalInstructionBoundary (machinePc 0x4bdc) theta sigma /\
  physicalMainDecodeBounds args /\ bv_unsigned sp = decodeStackPointer args /\
  bv_unsigned ((sp + BV 64 32)%bv) = decodeStackPointer args + 32 /\
  physicalRegisterShapes (seq_regs theta) zesu_sys_regs /\
  physicalRegisterShapes (seq_regs theta) writeSuccessOtherRegShapes /\
  physicalRegister64 (seq_regs theta) "x1" (Z_to_bv 64 (machinePc 0x4bdc)) /\
  physicalRegister64 (seq_regs theta) "x2" sp /\
  physicalSavedRegisters (seq_regs theta) (decodeSavedRegisters args) /\
  (exists a0 a1 a2 : bv 64,
    physicalRegister64 (seq_regs theta) "x10" a0 /\
    physicalRegister64 (seq_regs theta) "x11" a1 /\
    physicalRegister64 (seq_regs theta) "x12" a2) /\
  (exists allocatorPointer allocatorSize : bv 64,
    physicalMainDecodeFrame args sigma allocatorPointer allocatorSize) /\
  physicalMainDecodeObject successExitTail args outcome sigma /\
  (match outcome with
   | DecodeBoundarySuccess _ => True
   | DecodeBoundaryFailure => physicalMainHeapFailureExit args sigma /\
       physicalFootprintSeparated (physicalMainCommonFootprint args ++ physicalMainHeapFootprint)
   end) /\ traceResidual initial prefix (decodeTail args).

Definition decodeTerminationHypothesis
    (approvedProgram : gmap addr isla_trace) : Prop :=
  forall (program : gmap addr isla_trace),
    approvedProgram ⊆ program ->
  forall (decodeTail successExitTail : DecodeBoundaryArgs -> spec)
    (initial : spec) (prefix : list seq_label) (args : DecodeBoundaryArgs)
    (theta : seq_local_state) (sigma : seq_global_state),
    physicalMainDecodeEntry program decodeTail successExitTail initial prefix args theta sigma ->
    exists (steps : nat) (labels : list seq_label)
      (theta' : seq_local_state) (sigma' : seq_global_state)
      (outcome : DecodeBoundaryOutcome WriteSuccessObservation),
      @nsteps isla_lang steps ([theta], sigma) labels ([theta'], sigma') /\
      physicalMainDecodeExit program decodeTail successExitTail initial (prefix ++ labels)
        args outcome theta' sigma'.
Definition scopedCodeAgreement (program : gmap addr isla_trace)
    (code : list (Z * isla_trace)) : Prop :=
  Forall (fun entry => program !! Z_to_bv 64 entry.1 = Some entry.2) code.
Print Assumptions decodeTerminationHypothesis.

Print Assumptions physicalDecoderEntryBoundary.
Print Assumptions physicalMainDecodeEntry.
Print Assumptions physicalMainDecodeExit.
