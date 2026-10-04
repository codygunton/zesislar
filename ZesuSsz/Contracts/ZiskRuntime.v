From Coq Require Import Lists.List ZArith.ZArith Bool.Bool.

Open Scope Z_scope.

(** This file states a runtime contract. It does not prove the runtime.
    The selected ZisK source is fbbc69bcd2ea9a78d1a438b4a897bc48ff0b00a3.
    Sources:
    - ziskos/entrypoint/src/dma/memcpy.s:8-11;
    - transpilers/riscv/src/riscv2zisk_context.rs:1003-1048,2509-2537;
    - core/src/operations/dma_memcpy.rs:15-23;
    - core/src/mem.rs:161,877-968;
    - core/src/zisk_inst_builder.rs:185-192.
    The transpiler consumes the CSR marker and its following add together.
    It stores the count in EXTRA_PARAMS_ADDR before the copy.
    Mem::memcpy permits overlap through a temporary source buffer.
    It does not use scalar-read input fallback semantics. *)

Definition ziskMemcpyCsr : Z := 0x813.
Definition ziskExtraParamsAddress : Z := 0xa0400f00.
Definition ziskWordLimit : Z := 2 ^ 64.

(** Permissions concern one complete populated section.
    A readable section includes its stored header bytes.
    The special scalar free_input word does not replace these bytes. *)
Record ZiskRuntimePermissions : Type := {
  ziskReadableSection : Z -> Z -> Prop;
  ziskWritableSection : Z -> Z -> Prop
}.

(** Observations describe public runtime events.
    RAM writes remain memory effects, including writes to output RAM. *)
Record ZiskRuntimeState (Observation : Type) : Type := {
  ziskRuntimeMemory : Z -> Z;
  ziskRuntimeRegister : nat -> Z;
  ziskRuntimePc : Z;
  ziskRuntimeObservations : list Observation
}.

Arguments ziskRuntimeMemory {Observation} _ _.
Arguments ziskRuntimeRegister {Observation} _ _.
Arguments ziskRuntimePc {Observation} _.
Arguments ziskRuntimeObservations {Observation} _.

Record ZiskMemcpyArguments : Type := {
  ziskMemcpyDestination : Z;
  ziskMemcpySource : Z;
  ziskMemcpyLength : Z;
  ziskMemcpyReturnAddress : Z
}.

Definition ziskByte (value : Z) : Prop := 0 <= value < 256.
Definition ziskWord (value : Z) : Prop := 0 <= value < ziskWordLimit.

Definition ziskMemcpyRange (address count : Z) : Prop :=
  ziskWord address /\ 0 <= count /\ address + count <= ziskWordLimit.

Definition ziskMemcpyCopies (args : ZiskMemcpyArguments) : Prop :=
  ziskMemcpyLength args <> 0 /\
  ziskMemcpyDestination args <> ziskMemcpySource args.

Definition ziskMemcpyDomain (permissions : ZiskRuntimePermissions)
    (args : ZiskMemcpyArguments) : Prop :=
  ziskWord (ziskMemcpyDestination args) /\
  ziskWord (ziskMemcpySource args) /\
  ziskWord (ziskMemcpyLength args) /\
  ziskWord (ziskMemcpyReturnAddress args) /\
  Z.land (ziskMemcpyReturnAddress args) (-2) mod 4 = 0 /\
  ziskWritableSection permissions ziskExtraParamsAddress 8 /\
  (ziskMemcpyCopies args ->
    ziskMemcpyRange (ziskMemcpyDestination args) (ziskMemcpyLength args) /\
    ziskMemcpyRange (ziskMemcpySource args) (ziskMemcpyLength args) /\
    ziskReadableSection permissions (ziskMemcpySource args) (ziskMemcpyLength args) /\
    ziskWritableSection permissions (ziskMemcpyDestination args) (ziskMemcpyLength args)).

(** The count store precedes source sampling.
    This order also covers a source or destination that overlaps the scratch word. *)
Definition ziskMemcpyStagedMemory (args : ZiskMemcpyArguments)
    (memory : Z -> Z) (address : Z) : Z :=
  if (ziskExtraParamsAddress <=? address) &&
     (address <? ziskExtraParamsAddress + 8) then
    Z.land (Z.shiftr (ziskMemcpyLength args)
      (8 * (address - ziskExtraParamsAddress))) 255
  else memory address.

Definition ziskMemcpyMemory (args : ZiskMemcpyArguments)
    (memory : Z -> Z) (address : Z) : Z :=
  let staged := ziskMemcpyStagedMemory args memory in
  if (negb (ziskMemcpyLength args =? 0)) &&
     (negb (ziskMemcpyDestination args =? ziskMemcpySource args)) &&
     (ziskMemcpyDestination args <=? address) &&
     (address <? ziskMemcpyDestination args + ziskMemcpyLength args) then
    staged (ziskMemcpySource args + address - ziskMemcpyDestination args)
  else staged address.

Definition ziskMemcpyEntry {Observation}
    (permissions : ZiskRuntimePermissions) (entryPc : Z)
    (args : ZiskMemcpyArguments) (before : ZiskRuntimeState Observation) : Prop :=
  ziskMemcpyDomain permissions args /\
  ziskRuntimePc before = entryPc /\
  ziskRuntimeRegister before 0%nat = 0 /\
  ziskRuntimeRegister before 1%nat = ziskMemcpyReturnAddress args /\
  ziskRuntimeRegister before 10%nat = ziskMemcpyDestination args /\
  ziskRuntimeRegister before 11%nat = ziskMemcpySource args /\
  ziskRuntimeRegister before 12%nat = ziskMemcpyLength args /\
  (forall address, ziskByte (ziskRuntimeMemory before address)).

(** The service has no architectural integer-register clobbers.
    The tail jr uses the preserved caller return address.
    The resulting PC clears bit zero, as required by jalr.
    A caller continuation remains a separate logical resource.
    This predicate describes its return state without assuming its proof. *)
Definition ziskMemcpyExit {Observation} (args : ZiskMemcpyArguments)
    (before after : ZiskRuntimeState Observation) : Prop :=
  (forall address, ziskRuntimeMemory after address =
    ziskMemcpyMemory args (ziskRuntimeMemory before) address) /\
  (forall register, ziskRuntimeRegister after register =
    ziskRuntimeRegister before register) /\
  ziskRuntimePc after = Z.land (ziskMemcpyReturnAddress args) (-2) /\
  ziskRuntimeObservations after = ziskRuntimeObservations before.

(** The earlier D3 decision permits named ZisK CSR contract premises.
    The rung-2 trust text must state this exact service premise.
    This file supplies no service correctness or termination proof. *)
Record ZiskMemcpyServiceContract : Type := {
  ziskMemcpyEntryPc : Z;
  ziskMemcpyAllows : forall Observation : Type,
    ZiskRuntimePermissions -> ZiskMemcpyArguments ->
    ZiskRuntimeState Observation -> ZiskRuntimeState Observation -> Prop
}.

Arguments ziskMemcpyAllows _ {Observation} _ _ _ _.

Definition ziskMemcpyContract (entryPc : Z) : ZiskMemcpyServiceContract := {|
  ziskMemcpyEntryPc := entryPc;
  ziskMemcpyAllows := fun Observation permissions args before after =>
    ziskMemcpyEntry permissions entryPc args before /\
    ziskMemcpyExit args before after
|}.
