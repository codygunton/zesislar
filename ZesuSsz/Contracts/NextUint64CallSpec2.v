From Coq Require Import List ZArith.
From stdpp Require Import base list bitvector.definitions.
Require Import isla.riscv64.riscv64.
Require Import EvmSailRlp.evm_rlp_types.
Require Import ZesuSsz.Contracts.RlpDecodeItem.
Require Import ZesuSsz.Contracts.ParentHeaderRootFacts.
Require Import ZesuSsz.Contracts.NextUint64BlockEntries.
Require Import ZesuSsz.Automation2.Calls.
Require Export ZesuSsz.Contracts.DecodeItemCallData.
Open Scope Z_scope.
Open Scope stdpp_scope.

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

(* nextUint64ContractCorrect (NextUint64Contract.v) in the machine_call
   shape. Compliance/NextUint64CallSpec2.v derives it from that theorem.
   The slice at a1 is two 64-bit words, so the caller binds the input
   pointer and length from the words it stored there. *)
Definition nextUint64CallSpec2 `{!islaG Sigma} `{!threadG} : iProp Sigma :=
  (machine_call decodeItemCallMap nextUint64CallStackBytes
    (fun argv sp RET =>
      ∃ (inputPointer inputLength inputEndBits : bv 64) (input : list byte),
      "zisk_input_end" ↦ᵣ RVal_Bits inputEndBits ∗
      reg_col [(KindReg "zisk_free_input", BitsShape 64)] ∗
      bv_unsigned (argv !!! 1%nat) ↦ₘ inputPointer ∗
      (bv_unsigned (argv !!! 1%nat) + 8) ↦ₘ inputLength ∗
      bv_unsigned inputPointer ↦ₘ∗ input ∗
      bv_unsigned (argv !!! 0%nat) ↦ₘ? 16 ∗
      ⌜Z.of_nat (length input) = bv_unsigned inputLength⌝ ∗
      ⌜nextUint64BoundaryDomain
          (nextUint64CallDataArgs argv sp inputPointer inputEndBits input)⌝ ∗
      RET (fun _ =>
        ∃ result : NextUint64Return,
        "zisk_input_end" ↦ᵣ RVal_Bits inputEndBits ∗
        reg_col [(KindReg "zisk_free_input", BitsShape 64)] ∗
        bv_unsigned (argv !!! 1%nat) ↦ₘ Z_to_bv 64 (nextRestPointer result) ∗
        (bv_unsigned (argv !!! 1%nat) + 8) ↦ₘ Z_to_bv 64 (nextRestLength result) ∗
        bv_unsigned inputPointer ↦ₘ∗ input ∗
        bv_unsigned (argv !!! 0%nat) ↦ₘ∗ nextResultBytes result ∗
        ⌜nextUint64RootResult
            (nextUint64Base
              (nextUint64CallDataArgs argv sp inputPointer inputEndBits input))
            result⌝ ∗
        True)))%I.
Global Instance : LithiumUnfold (@nextUint64CallSpec2) := I.
Global Typeclasses Opaque nextUint64CallSpec2.
