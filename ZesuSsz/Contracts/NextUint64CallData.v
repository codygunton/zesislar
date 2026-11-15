From Coq Require Import List ZArith.
From stdpp Require Import base list bitvector.definitions.
Require Import EvmSailRlp.evm_rlp_types.
Require Import ZesuSsz.Contracts.ParentHeaderRootFacts.
Require Import ZesuSsz.Contracts.NextUint64BlockEntries.
Open Scope Z_scope.
Open Scope stdpp_scope.

(* Data of the nextUint64 call specs (no predicate): the stack size and the
   call data. ZesuSsz/Interfaces/NextUint64.v re-exports this module. *)

(* nextUint64 uses 96 bytes and its decodeItem call 16 more. *)
Notation nextUint64CallStackBytes := ((112) : Z) (only parsing).

(* The call data of a nextUint64 call. a0 is the result, a1 the slice.
   The slice holds the input pointer and length, so the input array is
   reached through memory: its pointer and length are the two words of
   the slice. The return address and the saved
   registers do not occur in the domain or the result relation. *)
Definition nextUint64CallDataArgs (argv : list (bv 64)) (sp : bv 64)
    (inputPointer inputEnd : bv 64) (input : list byte) : NextUint64Args :=
  {| nextUint64Base :=
       {| nextInputPointer := bv_unsigned inputPointer;
          nextInputBytes := input;
          nextSlicePointer := bv_unsigned (argv !!! 1%nat);
          nextResultPointer := bv_unsigned (argv !!! 0%nat);
          nextStackPointer := bv_unsigned sp;
          nextReturnAddress := 0;
          nextSavedS0 := Z_to_bv 64 0; nextSavedS1 := Z_to_bv 64 0;
          nextSavedS2 := Z_to_bv 64 0; nextSavedS3 := Z_to_bv 64 0;
          nextSavedS4 := Z_to_bv 64 0 |};
     nextUint64InputEnd := bv_unsigned inputEnd;
     nextUint64SavedX21 := Z_to_bv 64 0; nextUint64SavedX22 := Z_to_bv 64 0;
     nextUint64SavedX23 := Z_to_bv 64 0; nextUint64SavedX24 := Z_to_bv 64 0;
     nextUint64SavedX25 := Z_to_bv 64 0; nextUint64SavedX26 := Z_to_bv 64 0;
     nextUint64SavedX27 := Z_to_bv 64 0 |}.
