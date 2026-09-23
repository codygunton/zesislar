From Coq Require Import Lists.List.

Import ListNotations.

(** Reviewed divergence classes for the pinned Zesu endpoint. *)
Inductive KnownBug : Type :=
(* Zesu normalizes chain ID zero to one at [ssz.zig:405].  The reference
   decoder preserves the uint64 value through [evm_decoder.v:8284]. *)
| ChainIdZeroNormalization
(* Zesu accepts the legacy three-offset table at [ssz.zig:241].  The
   reference fixed-area bound is 20 bytes at [evm_decoder.v:7136]. *)
| LegacyRequestTableArity
(* Zesu accepts the 528-byte V3 payload at [ssz.zig:266].  The reference
   fixed-area bound is 540 bytes at [evm_decoder.v:7134]. *)
| LegacyPayloadSize
(* Zesu records activation values at [ssz.zig:198-199].  The reference
   requires activation at or before the payload at [evm_decoder.v:8267,8276]. *)
| FutureForkActivation
(* Zesu copies unbounded extra data at [ssz.zig:318].  The reference bound
   is 2^5 bytes at [evm_decoder.v:7146]. *)
| ExtraDataLength
(* Zesu computes an unbounded key count at [ssz.zig:364].  The reference
   bound is 2^15 keys at [evm_decoder.v:7170]. *)
| PublicKeyCount
(* Zesu computes an unbounded hash count at [ssz.zig:228].  The reference
   bound is 2^12 hashes at [evm_decoder.v:7156]. *)
| VersionedHashCount
(* The reference permits at most 2^4 withdrawals [evm_decoder.v:7152]. *)
| WithdrawalCount
(* The reference permits at most 2^20 transactions [evm_decoder.v:7150]. *)
| TransactionCount
(* The reference permits at most 2^8 witness headers [evm_decoder.v:7166]. *)
| WitnessHeaderCount.

(** This fixed list prevents later proofs from adding exceptions. *)
Definition knownBugs : list KnownBug :=
  [ ChainIdZeroNormalization; LegacyRequestTableArity; LegacyPayloadSize;
    FutureForkActivation; ExtraDataLength; PublicKeyCount;
    VersionedHashCount; WithdrawalCount; TransactionCount;
    WitnessHeaderCount ].
