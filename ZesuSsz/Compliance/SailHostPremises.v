From Coq Require Import List ZArith.
From stdpp Require Import bitvector.definitions.
Require Import SailStdpp.MachineWord.
Require Import EvmSail.evm_decoder_types.
Import ListNotations.
Open Scope Z_scope.

(* This is a host-state model for the seven approved C4 premises. It is not
   a body for any generated Sail extern. The bridge from each generated
   module's M action to these relations remains a separate obligation. *)
Record SailHostState (U : Type) := {
  hostInput : list byte;
  hostScratchCapacity : Z;
  hostScratchUsed : Z;
  hostScratchByte : Z -> byte;
  hostOther : U
}.

Arguments hostInput {U} _.
Arguments hostScratchCapacity {U} _.
Arguments hostScratchUsed {U} _.
Arguments hostScratchByte {U} _ _.
Arguments hostOther {U} _.

Definition hostScratchSlice {U} (s : SailHostState U) (off len : Z) : list byte :=
  map (fun k => hostScratchByte s (off + Z.of_nat k)) (seq 0 (Z.to_nat len)).

Definition hostInputSlice {U} (s : SailHostState U) (off len : Z) : list byte :=
  firstn (Z.to_nat len) (skipn (Z.to_nat off) (hostInput s)).

Definition hostWordByte (value len index : Z) : byte :=
  Z_to_bv 8 (Z.shiftr value (8 * (len - 1 - index))).

(* The relations name the actions that a generated decoder must use.
   Each relation's behavioral premise below requires a completed result. *)
Record SailHostOperations (U : Type) := {
  hostReserve : SailHostState U -> Z -> Z -> SailHostState U -> bool -> Prop;
  hostStoreByte : SailHostState U -> Z -> byte -> SailHostState U -> Z -> Prop;
  hostStoreInput : SailHostState U -> Z -> Z -> Z -> SailHostState U -> Z -> Prop;
  hostStoreWord : SailHostState U -> Z -> Z -> Z -> SailHostState U -> Z -> Prop;
  hostTruncate : SailHostState U -> Z -> SailHostState U -> unit -> Prop;
  hostScratchKeccak : SailHostState U -> Z -> Z -> SailHostState U -> hash -> Prop;
  hostInputKeccak : SailHostState U -> Z -> Z -> SailHostState U -> hash -> Prop
}.

Arguments hostReserve {U} _ _ _ _ _ _.
Arguments hostStoreByte {U} _ _ _ _ _ _.
Arguments hostStoreInput {U} _ _ _ _ _ _ _.
Arguments hostStoreWord {U} _ _ _ _ _ _ _.
Arguments hostTruncate {U} _ _ _ _ _.
Arguments hostScratchKeccak {U} _ _ _ _ _ _.
Arguments hostInputKeccak {U} _ _ _ _ _ _.

(* The digest function is an explicit C4 input. No theorem here proves that
   it implements Keccak-256. Every premise preserves input and other state;
   the hash and reserve premises preserve the complete host state. *)
Record SailHostPremises {U : Type} (ops : SailHostOperations U)
    (digest : list byte -> hash) : Prop := {
  host_scratch_reserve_premise :
    forall s off len,
      0 <= off /\ 0 <= len /\ off <= hostScratchCapacity s ->
      exists s' accepted,
        hostReserve ops s off len s' accepted /\
        s' = s /\ accepted = Z.leb (off + len) (hostScratchCapacity s);

  host_scratch_store_byte_premise :
    forall s off value,
      0 <= off < hostScratchCapacity s ->
      exists s' returnedLength,
        hostStoreByte ops s off value s' returnedLength /\
        returnedLength = off + 1 /\
        hostScratchUsed s' = off + 1 /\
        hostScratchCapacity s' = hostScratchCapacity s /\
        hostInput s' = hostInput s /\ hostOther s' = hostOther s /\
        (forall address, hostScratchByte s' address =
          if Z.eqb address off then value else hostScratchByte s address);

  host_scratch_store_stateless_input_premise :
    forall s dst off len,
      0 <= dst /\ 0 <= off /\ 0 <= len /\
      dst + len <= hostScratchCapacity s /\
      off + len <= Z.of_nat (length (hostInput s)) ->
      exists s' returnedLength,
        hostStoreInput ops s dst off len s' returnedLength /\
        returnedLength = dst + len /\
        hostScratchUsed s' = dst + len /\
        hostScratchCapacity s' = hostScratchCapacity s /\
        hostInput s' = hostInput s /\ hostOther s' = hostOther s /\
        (forall address,
          hostScratchByte s' address =
            if (dst <=? address) && (address <? dst + len)
            then nth (Z.to_nat (off + address - dst)) (hostInput s) (Z_to_bv 8 0)
            else hostScratchByte s address);

  host_scratch_store_word_premise :
    forall s off value len,
      0 <= off /\ 0 <= len <= 32 /\
      off + len <= hostScratchCapacity s ->
      exists s' returnedLength,
        hostStoreWord ops s off value len s' returnedLength /\
        returnedLength = off + len /\
        hostScratchUsed s' = off + len /\
        hostScratchCapacity s' = hostScratchCapacity s /\
        hostInput s' = hostInput s /\ hostOther s' = hostOther s /\
        (forall address,
          hostScratchByte s' address =
            if (off <=? address) && (address <? off + len)
            then hostWordByte value len (address - off)
            else hostScratchByte s address);

  host_scratch_truncate_premise :
    forall s mark,
      0 <= mark <= hostScratchUsed s ->
      exists s' returned,
        hostTruncate ops s mark s' returned /\
        returned = tt /\ hostScratchUsed s' = mark /\
        hostScratchCapacity s' = hostScratchCapacity s /\
        hostInput s' = hostInput s /\ hostOther s' = hostOther s /\
        (forall address, 0 <= address < mark ->
          hostScratchByte s' address = hostScratchByte s address);

  scratch_keccak256_premise :
    forall s off len,
      0 <= off /\ 0 <= len /\ off + len <= hostScratchUsed s ->
      exists s' result,
        hostScratchKeccak ops s off len s' result /\
        s' = s /\ result = digest (hostScratchSlice s off len);

  stateless_input_keccak256_premise :
    forall s off len,
      0 <= off /\ 0 <= len /\
      off + len <= Z.of_nat (length (hostInput s)) ->
      exists s' result,
        hostInputKeccak ops s off len s' result /\
        s' = s /\ result = digest (hostInputSlice s off len)
}.
