From Coq Require Import Strings.String Lists.List ZArith.ZArith.

Import ListNotations.

(* Each loaded extent uses an exclusive end address. *)
Record MachineSection : Type := {
  sectionBase : Z; sectionEnd : Z; sectionFileEnd : Z;
  sectionReadable : bool; sectionWritable : bool; sectionExecutable : bool
}.

(** The map selects layout and platform configuration independently of instruction semantics. *)
Record MachineMap : Type := {
  mapPopulatedSections : list MachineSection;
  mapRamBase : Z; mapRamSize : Z;
  mapTextBase : Z; mapTextEnd : Z;
  mapRodataBase : Z; mapRodataEnd : Z;
  mapDataBase : Z;
  mapHeapBase : Z; mapHeapEnd : Z;
  mapInputBufferAddress : Z; mapInputCapacity : Z;
  mapIoContextAddress : option Z;
  mapStartPc : Z; mapReadInputPc : option Z; mapWriteOutputPc : option Z;
  mapZkvmExitPc : option Z; mapMemcpyPc : Z; mapMainPc : Z;
  mapHeapTopAddress : Z; mapHeapPosAddress : Z;
  mapRomBase : Z; mapRomSize : Z;
  mapClintBase : Z; mapClintSize : Z;
  mapHtifTohost : Z;
  mapEnableWritableMisa : bool; mapEnableRvc : bool; mapEnableFdext : bool;
  mapEnablePmp : bool; mapEnableDirtyUpdate : bool;
  mapEnableMisalignedAccess : bool; mapMtvalHasIllegalInstBits : bool;
  mapInsnsPerTick : Z;
  mapZiskPlatform : bool;
  mapPrivilege : string; mapMisa : Z; mapMtvec : Z;
  mapMstatusMask : Z; mapMstatusValue : Z
}.

Definition forkMap : MachineMap := {|
  mapPopulatedSections := [];
  mapRamBase := 0; mapRamSize := 0x40000000;
  mapTextBase := 0x10120; mapTextEnd := 0x171f8;
  mapRodataBase := 0x17200; mapRodataEnd := 0x179cc;
  mapDataBase := 0x19000;
  mapHeapBase := 0x1a000; mapHeapEnd := 0x2001a000;
  mapInputBufferAddress := 0x2001a000; mapInputCapacity := 0x04000000;
  mapIoContextAddress := Some 0x2401a0b8%Z;
  mapStartPc := 0x10120; mapReadInputPc := Some 0x10140%Z;
  mapWriteOutputPc := Some 0x10190%Z; mapZkvmExitPc := Some 0x101c4%Z;
  mapMemcpyPc := 0x101d4; mapMainPc := 0x14cb0;
  mapHeapTopAddress := 0x19000; mapHeapPosAddress := 0x19008;
  mapRomBase := 0x40002000; mapRomSize := 0x100;
  mapClintBase := 0x40010000; mapClintSize := 0xc0000;
  mapHtifTohost := 0x40001000;
  mapEnableWritableMisa := true; mapEnableRvc := false; mapEnableFdext := false;
  mapEnablePmp := false; mapEnableDirtyUpdate := false;
  mapEnableMisalignedAccess := false; mapMtvalHasIllegalInstBits := false;
  mapInsnsPerTick := 10; mapZiskPlatform := false;
  mapPrivilege := "Machine"%string;
  mapMisa := 0x8000000000001100; mapMtvec := 0;
  mapMstatusMask := 0x20000; mapMstatusValue := 0
|}.

(* BEGIN GENERATED STOCK MAP *)
(** ELF SHA256: e44c18d54ae3d77832df92aceb6eb7119de8eb2e8f1f1b4e585a6e33ea04ff95. *)
Definition defaultMap : MachineMap := {|
  mapPopulatedSections := [
    {| sectionBase := 0x80000000; sectionEnd := 0x8010fd78; sectionFileEnd := 0x8010fd78; sectionReadable := false; sectionWritable := false; sectionExecutable := true |};
    {| sectionBase := 0x8010fd80; sectionEnd := 0x80118678; sectionFileEnd := 0x80118678; sectionReadable := true; sectionWritable := false; sectionExecutable := false |};
    {| sectionBase := 0xa0430000; sectionEnd := 0xa0d34520; sectionFileEnd := 0xa0430000; sectionReadable := true; sectionWritable := true; sectionExecutable := false |};
    {| sectionBase := 0xa0d34520; sectionEnd := 0xa0d34530; sectionFileEnd := 0xa0d34530; sectionReadable := true; sectionWritable := true; sectionExecutable := false |}
  ];
  mapRamBase := 0xa0000000;
  mapRamSize := 0x20000000;
  mapTextBase := 0x80000000;
  mapTextEnd := 0x8010fd78;
  mapRodataBase := 0x8010fd80;
  mapRodataEnd := 0x80118678;
  mapDataBase := 0xa0430000;
  mapHeapBase := 0xa0d34530;
  mapHeapEnd := 0xbfff0000;
  mapInputBufferAddress := 0x40000000;
  mapInputCapacity := 0x40000000;
  mapIoContextAddress := None;
  mapStartPc := 0x800f5b30;
  mapReadInputPc := Some 0x800e1720%Z;
  mapWriteOutputPc := Some 0x800e17b8%Z;
  mapZkvmExitPc := None;
  mapMemcpyPc := 0x800e06c0;
  mapMainPc := 0x80041ee0;
  mapHeapTopAddress := 0xa0d34528;
  mapHeapPosAddress := 0xa0d34520;
  mapRomBase := 0x0;
  mapRomSize := 0x0;
  mapClintBase := 0x0;
  mapClintSize := 0x0;
  mapHtifTohost := 0x0;
  mapEnableWritableMisa := true;
  mapEnableRvc := false;
  mapEnableFdext := false;
  mapEnablePmp := false;
  mapEnableDirtyUpdate := false;
  mapEnableMisalignedAccess := true;
  mapMtvalHasIllegalInstBits := false;
  mapInsnsPerTick := 0xa;
  mapZiskPlatform := true;
  mapPrivilege := "Machine"%string;
  mapMisa := 0x8000000000001100;
  mapMtvec := 0x0;
  mapMstatusMask := 0x20000;
  mapMstatusValue := 0x0
|}.
Definition stockZiskMap := defaultMap.
(* END GENERATED STOCK MAP *)


Definition machineRamEnd (machine : MachineMap) : Z :=
  (mapRamBase machine + mapRamSize machine)%Z.
Definition machinePcFor (machine : MachineMap) (offset : Z) : Z :=
  (mapTextBase machine + offset)%Z.
Definition machinePc (offset : Z) : Z := (mapTextBase defaultMap + offset)%Z.
Definition machineOutputAddress (machine : MachineMap) : option Z :=
  option_map (fun address => (address + 8)%Z) (mapIoContextAddress machine).
Definition machineOutputSizeAddress (machine : MachineMap) : option Z :=
  option_map (fun address => (address + 16)%Z) (mapIoContextAddress machine).
Definition machineExitAddress (machine : MachineMap) : option Z :=
  option_map (fun address => (address + 24)%Z) (mapIoContextAddress machine).

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
