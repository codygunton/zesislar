From Coq Require Import List ZArith.
From stdpp Require Import base list bitvector.definitions.
Require Import isla.riscv64.riscv64.
Require Import EvmSailRlp.evm_rlp_types.
Require Import ZesuSsz.Contracts.AbiBytes.
Require Import ZesuSsz.Contracts.ZiskRuntime.
Require Import ZesuSsz.Contracts.AltFlAllocPremises.
Require Import ZesuSsz.Automation2.Calls.
Require Export ZesuSsz.Contracts.DecodeItemCallData.
Require Export ZesuSsz.Contracts.ArrayListContract.
Open Scope Z_scope.
Open Scope stdpp_scope.

(* The contract arguments of a call: a0 = result, a1 = list, a2 = allocator
   object (argv), the stack pointer and return address of the call, the
   callee-saved registers it preserves, and the owned memory values. *)
Definition entriesToOwnedSliceCallArgs (argv : list (bv 64)) (sp ret inputEnd : bv 64)
    (saved : ArrayListCalleeSaved) (context : Z) (state : ArrayListState)
    (resultBefore scratchBefore : list byte) : ToOwnedSliceArgs :=
  {| toOwnedResultPointer := argv !!! 0%nat;
     toOwnedListPointer := argv !!! 1%nat;
     toOwnedAllocatorPointer := argv !!! 2%nat;
     toOwnedAllocatorContext := context;
     toOwnedList := state;
     toOwnedResultBefore := resultBefore;
     toOwnedScratchBefore := scratchBefore;
     toOwnedStackPointer := sp;
     toOwnedInputEnd := inputEnd;
     toOwnedReturnAddress := ret;
     toOwnedSaved := saved |}.

(* The domain of toOwnedSliceDomain without its stack and return-address
   conjuncts, which machine_call states. *)
Definition entriesToOwnedSliceBoundaryDomain (argv : list (bv 64)) (context : Z)
    (state : ArrayListState) (resultBefore scratchBefore : list byte) : Prop :=
  arrayListWellFormed entriesElementBytes state /\
  arrayListRamRange (bv_unsigned (argv !!! 0%nat)) arrayListResultSize /\
  (8 | bv_unsigned (argv !!! 0%nat)) /\
  arrayListRamRange (bv_unsigned (argv !!! 1%nat)) arrayListHeaderSize /\
  (8 | bv_unsigned (argv !!! 1%nat)) /\
  arrayListRamRange (bv_unsigned (argv !!! 2%nat)) arrayListAllocatorSize /\
  (8 | bv_unsigned (argv !!! 2%nat)) /\
  Z.of_nat (length resultBefore) = arrayListResultSize /\
  Z.of_nat (length scratchBefore) = arrayListScratchSize /\
  0 <= context < 2 ^ 64.

(* The outcome relation of toOwnedSliceAllows; it reads only the list state
   and the result bytes of its arguments. *)
Definition entriesToOwnedSliceBoundaryAllows (state : ArrayListState) (resultBefore : list byte)
    (outcome : ToOwnedSliceOutcome) : Prop :=
  toOwnedSliceAllows entriesElementBytes entriesEmptyPointer
    (entriesToOwnedSliceCallArgs [] (BV 64 0) (BV 64 0) (BV 64 0)
      {| savedX8 := BV 64 0; savedX9 := BV 64 0; savedX18 := BV 64 0;
         savedX19 := BV 64 0; savedX20 := BV 64 0; savedX21 := BV 64 0;
         savedX22 := BV 64 0; savedX23 := BV 64 0; savedX24 := BV 64 0;
         savedX25 := BV 64 0; savedX26 := BV 64 0; savedX27 := BV 64 0 |}
      0 state resultBefore [])
    outcome.

(* The template of entriesToOwnedSlice's public call spec:
   EntriesToOwnedSliceContractCorrect (EntriesToOwnedSliceContract.v) in the
   machine_call shape. Callers never import this module: the public spec
   entriesToOwnedSliceCallSpec2 is rendered from this body in
   ZesuSsz/Interfaces/EntriesToOwnedSlice.v (tools/block/render_interfaces.py,
   registry ZesuSsz/Contracts/proved_functions.json).
   Compliance/EntriesToOwnedSliceCallSpec2.v derives this template from that
   theorem. *)
Definition entriesToOwnedSliceCallSpecDefinition `{!islaG Sigma} `{!threadG} : iProp Sigma :=
  (machine_call decodeItemCallMap arrayListToOwnedSliceStackBytes
    (fun argv sp RET =>
      ∃ (inputEndBits : bv 64) (context : Z) (state : ArrayListState)
        (resultBefore scratchBefore : list byte),
      "zisk_input_end" ↦ᵣ RVal_Bits inputEndBits ∗
      reg_col [(KindReg "zisk_free_input", BitsShape 64)] ∗
      bv_unsigned (argv !!! 1%nat) ↦ₘ∗ arrayListHeaderBytes state ∗
      arrayListBuffer entriesElementBytes entriesLog2Alignment state ∗
      bv_unsigned (argv !!! 0%nat) ↦ₘ∗ resultBefore ∗
      ziskExtraParamsAddress ↦ₘ∗ scratchBefore ∗
      altFlAllocatorObject (bv_unsigned (argv !!! 2%nat)) context ∗
      altFlVtable ∗
      altFlHeap ∗
      ⌜entriesToOwnedSliceBoundaryDomain argv context state resultBefore scratchBefore⌝ ∗
      RET (fun _ =>
        ∃ outcome : ToOwnedSliceOutcome,
        "zisk_input_end" ↦ᵣ RVal_Bits inputEndBits ∗
        reg_col [(KindReg "zisk_free_input", BitsShape 64)] ∗
        bv_unsigned (argv !!! 1%nat) ↦ₘ∗ arrayListHeaderBytes (toOwnedListAfter outcome) ∗
        arrayListBuffer entriesElementBytes entriesLog2Alignment (toOwnedListAfter outcome) ∗
        arrayListBuffer entriesElementBytes entriesLog2Alignment (toOwnedSlice outcome) ∗
        bv_unsigned (argv !!! 0%nat) ↦ₘ∗ toOwnedResultAfter outcome ∗
        ziskExtraParamsAddress ↦ₘ∗
          (if arrayListLength state =? 0 then scratchBefore
           else match toOwnedKind outcome with
                | arrayListSuccess => word64Bytes (arrayListLength state * entriesElementBytes)
                | arrayListOutOfMemory => scratchBefore
                end) ∗
        altFlAllocatorObject (bv_unsigned (argv !!! 2%nat)) context ∗
        altFlVtable ∗
        altFlHeap ∗
        ⌜entriesToOwnedSliceBoundaryAllows state resultBefore outcome⌝ ∗
        True)))%I.

(* Inside the sealed interface the public spec is this template, so a proof
   of the template is a proof of the public spec. *)
Lemma entriesToOwnedSliceCallSpecCorrectFrom `{!islaG Sigma} `{!threadG} (code : iProp Sigma) (entry : Z) :
  (⊢ code -∗ instr_body entry entriesToOwnedSliceCallSpecDefinition) ->
  ⊢ code -∗ instr_body entry entriesToOwnedSliceCallSpecDefinition.
Proof. exact id. Qed.
