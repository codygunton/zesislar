From Coq Require Import Lists.List.

Import ListNotations.

(** Reviewed divergence classes for the pinned Zesu endpoint. *)
Inductive KnownBug : Type :=
| ChainIdZeroNormalization
| LegacyRequestTableArity
| LegacyPayloadSize
| FutureForkActivation
| ExtraDataLength
| PublicKeyCount
| VersionedHashCount.

(** This fixed list prevents later proofs from adding exceptions. *)
Definition knownBugs : list KnownBug :=
  [ ChainIdZeroNormalization; LegacyRequestTableArity; LegacyPayloadSize;
    FutureForkActivation; ExtraDataLength; PublicKeyCount;
    VersionedHashCount ].
