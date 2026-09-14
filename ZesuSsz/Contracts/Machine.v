From Coq Require Import Strings.String Lists.List ZArith.ZArith.

Import ListNotations.

(** Machine addresses come from the pinned ELF's section and symbol tables.
    .text: [0x10120,0x171f8); .rodata: [0x17200,0x179cc);
    .sdata: [0x19000,0x19010); heap_buffer: [0x1a000,0x2001a000);
    input_buffer: [0x2001a000,0x2401a000); binary_fv_io_context:
    [0x2401a0b8,0x2401a0d8). Evidence: readelf -S/-l and nm -n on
    zesu-ssz-decode-bare-metal-rv64im-elf-d67f28c. The default ELF stays
    frozen through CP5. CLINT and ROM lie outside RAM. *)
Record MachineMap : Type := {
  mapRamBase : Z; mapRamSize : Z;
  mapTextBase : Z; mapTextEnd : Z;
  mapRodataBase : Z; mapRodataEnd : Z;
  mapDataBase : Z;
  mapHeapBase : Z; mapHeapEnd : Z;
  mapInputBufferAddress : Z; mapInputCapacity : Z;
  mapIoContextAddress : Z;
  mapStartPc : Z; mapReadInputPc : Z; mapWriteOutputPc : Z;
  mapZkvmExitPc : Z; mapMemcpyPc : Z; mapMainPc : Z;
  mapHeapTopAddress : Z; mapHeapPosAddress : Z;
  mapRomBase : Z; mapRomSize : Z;
  mapClintBase : Z; mapClintSize : Z;
  mapHtifTohost : Z;
  mapEnableWritableMisa : bool; mapEnableRvc : bool; mapEnableFdext : bool;
  mapEnablePmp : bool; mapEnableDirtyUpdate : bool;
  mapEnableMisalignedAccess : bool; mapMtvalHasIllegalInstBits : bool;
  mapInsnsPerTick : Z;
  mapPrivilege : string; mapMisa : Z; mapMtvec : Z;
  mapMstatusMask : Z; mapMstatusValue : Z
}.

Definition defaultMap : MachineMap := {|
  mapRamBase := 0; mapRamSize := 0x40000000;
  mapTextBase := 0x10120; mapTextEnd := 0x171f8;
  mapRodataBase := 0x17200; mapRodataEnd := 0x179cc;
  mapDataBase := 0x19000;
  mapHeapBase := 0x1a000; mapHeapEnd := 0x2001a000;
  mapInputBufferAddress := 0x2001a000; mapInputCapacity := 0x04000000;
  mapIoContextAddress := 0x2401a0b8;
  mapStartPc := 0x10120; mapReadInputPc := 0x10140;
  mapWriteOutputPc := 0x10190; mapZkvmExitPc := 0x101c4;
  mapMemcpyPc := 0x101d4; mapMainPc := 0x14cb0;
  mapHeapTopAddress := 0x19000; mapHeapPosAddress := 0x19008;
  mapRomBase := 0x40002000; mapRomSize := 0x100;
  mapClintBase := 0x40010000; mapClintSize := 0xc0000;
  mapHtifTohost := 0x40001000;
  mapEnableWritableMisa := true; mapEnableRvc := false; mapEnableFdext := false;
  mapEnablePmp := false; mapEnableDirtyUpdate := false;
  mapEnableMisalignedAccess := false; mapMtvalHasIllegalInstBits := false;
  mapInsnsPerTick := 10;
  mapPrivilege := "Machine"%string;
  mapMisa := 0x8000000000001100; mapMtvec := 0;
  mapMstatusMask := 0x20000; mapMstatusValue := 0
|}.

Definition machineRamEnd (machine : MachineMap) : Z :=
  (mapRamBase machine + mapRamSize machine)%Z.
Definition machinePc (offset : Z) : Z := (mapTextBase defaultMap + offset)%Z.
Definition machineOutputAddress (machine : MachineMap) : Z :=
  (mapIoContextAddress machine + 8)%Z.
Definition machineOutputSizeAddress (machine : MachineMap) : Z :=
  (mapIoContextAddress machine + 16)%Z.
Definition machineExitAddress (machine : MachineMap) : Z :=
  (mapIoContextAddress machine + 24)%Z.

(** Reduce derived addresses when instruction automation simplifies resources. *)
Arguments machineRamEnd _ /.
Arguments machinePc _ /.
Arguments machineOutputAddress _ /.
Arguments machineOutputSizeAddress _ /.
Arguments machineExitAddress _ /.

(** A machine contract describes one binary region without selecting a proof method. *)
Record RelationalMachineContract
    (State Args Outcome : Type) : Type := {
  contractAllows : Args -> Outcome -> Prop;
  contractEntry : Args -> State -> Prop;
  contractExit : Args -> Outcome -> State -> State -> Prop;
  contractStepBound : Args -> nat
}.

Inductive ConfinedTrace {State : Type}
    (step : nat -> State -> State -> Prop)
    (pc : State -> option Z)
    (region : Z -> Prop) : nat -> nat -> State -> State -> Prop :=
| ConfinedTraceRefl fromStep state :
    ConfinedTrace step pc region fromStep 0 state state
| ConfinedTraceStep fromStep count address before middle after :
    pc before = Some address ->
    region address ->
    step fromStep before middle ->
    ConfinedTrace step pc region (S fromStep) count middle after ->
    ConfinedTrace step pc region fromStep (S count) before after.

Definition ContractImplements {State Args Outcome : Type}
    (step : nat -> State -> State -> Prop)
    (pc : State -> option Z)
    (region exitPc : Z -> Prop)
    (contract : RelationalMachineContract State Args Outcome) : Prop :=
  forall args (fromStep : nat) before,
    contractEntry State Args Outcome contract args before ->
    exists (count : nat) after outcome,
      0 < count /\
      count <= contractStepBound State Args Outcome contract args /\
      ConfinedTrace step pc region fromStep count before after /\
      (exists address, pc after = Some address /\ exitPc address) /\
      contractAllows State Args Outcome contract args outcome /\
      contractExit State Args Outcome contract args outcome before after.

Definition PcInRanges (ranges : list (Z * Z)) (pc : Z) : Prop :=
  exists lower upper, In (lower, upper) ranges /\ (lower <= pc < upper)%Z.

Definition PcInList (pcs : list Z) (pc : Z) : Prop := In pc pcs.

Inductive InstructionPathFollows (nextPc : Z -> Z -> Prop) :
    list Z -> Prop :=
| InstructionPathOne pc : InstructionPathFollows nextPc [pc]
| InstructionPathNext fromPc toPc rest :
    nextPc fromPc toPc ->
    InstructionPathFollows nextPc (toPc :: rest) ->
    InstructionPathFollows nextPc (fromPc :: toPc :: rest).

Definition StraightLineInstructionStep (fromPc toPc : Z) : Prop :=
  (toPc = fromPc + 4)%Z.

(** A finite path certifies the instruction bound separately from the
    Islaris resource proof. The path contains its terminal PC. *)
Definition InstructionPathCertificate
    (nextPc : Z -> Z -> Prop) (region exitPc : Z -> Prop)
    (entryPc : Z) (bound : nat) : Prop :=
  exists instructionPath : list Z,
    hd_error instructionPath = Some entryPc /\
    InstructionPathFollows nextPc instructionPath /\
    Forall region (removelast instructionPath) /\
    (exists pc, last instructionPath entryPc = pc /\ exitPc pc) /\
    length instructionPath = S bound /\
    0 < bound.

(** The bridge keeps state correctness and termination as separate proofs. *)
Record NativeContractAssumption
    (correctness : Prop)
    (nextPc : Z -> Z -> Prop) (region exitPc : Z -> Prop)
    (entryPc : Z) (bound : nat) : Prop := {
  nativeStateCorrect : correctness;
  nativeTermination :
    InstructionPathCertificate nextPc region exitPc entryPc bound
}.

Lemma nativeContractBridge
    (correctness : Prop)
    (nextPc : Z -> Z -> Prop) (region exitPc : Z -> Prop)
    (entryPc : Z) (bound : nat) :
  correctness ->
  InstructionPathCertificate nextPc region exitPc entryPc bound ->
  NativeContractAssumption correctness nextPc region exitPc entryPc bound.
Proof. constructor; assumption. Qed.
