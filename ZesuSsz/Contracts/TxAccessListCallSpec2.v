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
Require Export ZesuSsz.Contracts.TxAccessListContract.
Open Scope Z_scope.
Open Scope stdpp_scope.

(* The 576-byte frame and the 128 bytes of the callee frames below it
   (TxAccessListContract.v). *)
Notation txAccessListStackBytes := ((576 + 128) : Z) (only parsing).

(* The contract arguments of a call: a0 = result, a1 = allocator object,
   a2 = the `rest` slice cell (argv), the stack pointer and return address of
   the call, the end of the input region, the callee-saved registers it
   preserves, and the owned memory values: the allocator context, the input
   slice the `rest` cell holds and its bytes, and the scratch word. *)
Definition txAccessListCallArgs (argv : list (bv 64)) (sp ret inputEnd : bv 64)
    (saved : ArrayListCalleeSaved) (context inputPointer inputLength : bv 64)
    (input scratchBefore : list byte) : TxAccessListArgs :=
  {| txResultPointer := argv !!! 0%nat;
     txAllocatorPointer := argv !!! 1%nat;
     txRestPointer := argv !!! 2%nat;
     txAllocatorContext := context;
     txInputPointer := inputPointer;
     txInputLength := inputLength;
     txInputBytes := input;
     txInputEnd := inputEnd;
     txStackPointer := sp;
     txReturnAddress := ret;
     txSavedX8 := savedX8 saved; txSavedX9 := savedX9 saved;
     txSavedX18 := savedX18 saved; txSavedX19 := savedX19 saved;
     txSavedX20 := savedX20 saved; txSavedX21 := savedX21 saved;
     txSavedX22 := savedX22 saved; txSavedX23 := savedX23 saved;
     txSavedX24 := savedX24 saved; txSavedX25 := savedX25 saved;
     txSavedX26 := savedX26 saved; txSavedX27 := savedX27 saved;
     txScratchBefore := scratchBefore |}.

(* The callee-saved placeholder of the domain and the outcome relation, which
   read no saved register. *)
Definition txAccessListNoSaved : ArrayListCalleeSaved :=
  {| savedX8 := BV 64 0; savedX9 := BV 64 0; savedX18 := BV 64 0;
     savedX19 := BV 64 0; savedX20 := BV 64 0; savedX21 := BV 64 0;
     savedX22 := BV 64 0; savedX23 := BV 64 0; savedX24 := BV 64 0;
     savedX25 := BV 64 0; savedX26 := BV 64 0; savedX27 := BV 64 0 |}.

(* The template of txAccessList's public call spec: TxAccessListContractCorrect
   (TxAccessListContract.v) in the machine_call shape. The domain is the
   contract's well-formedness at the call's arguments: it names the stack
   pointer (the frame's separation from the argument ranges), which
   machine_call does not state. The return address is machine_call's; the
   contract reads it only for its alignment (machine_call states it), so the
   domain and the outcome relation take the placeholder 0, and
   txAccessListNoSaved for the callee-saved registers. Callers never import this module: the public
   spec txAccessListCallSpec2 is rendered from this body in
   ZesuSsz/Interfaces/TxAccessList.v (tools/block/render_interfaces.py,
   registry ZesuSsz/Contracts/proved_functions.json).
   Compliance/TxAccessListCallSpec2.v derives this template from that
   theorem. *)
Definition txAccessListCallSpecDefinition `{!islaG Sigma} `{!threadG} : iProp Sigma :=
  (machine_call decodeItemCallMap txAccessListStackBytes
    (fun argv sp RET =>
      ∃ (inputEndBits : bv 64)
        (context inputPointer inputLength : bv 64) (input scratchBefore : list byte),
      "zisk_input_end" ↦ᵣ RVal_Bits inputEndBits ∗
      reg_col [(KindReg "zisk_free_input", BitsShape 64)] ∗
      bv_unsigned inputPointer ↦ₘ∗ input ∗
      bv_unsigned (argv !!! 2%nat) ↦ₘ∗
        (word64Bytes (bv_unsigned inputPointer) ++ word64Bytes (bv_unsigned inputLength)) ∗
      altFlAllocatorObject (bv_unsigned (argv !!! 1%nat)) (bv_unsigned context) ∗
      altFlVtable ∗
      altFlHeap ∗
      ziskExtraParamsAddress ↦ₘ∗ scratchBefore ∗
      bv_unsigned (argv !!! 0%nat) ↦ₘ? txAccessListResultSize ∗
      ⌜txAccessListArgsWellFormed
         (txAccessListCallArgs argv sp (BV 64 0) inputEndBits txAccessListNoSaved context inputPointer
            inputLength input scratchBefore)⌝ ∗
      RET (fun _ =>
        ∃ outcome : TxAccessListOutcome,
        "zisk_input_end" ↦ᵣ RVal_Bits inputEndBits ∗
        reg_col [(KindReg "zisk_free_input", BitsShape 64)] ∗
        bv_unsigned inputPointer ↦ₘ∗ input ∗
        bv_unsigned (argv !!! 2%nat) ↦ₘ∗
          (word64Bytes (bv_unsigned inputPointer + txConsumed outcome) ++
           word64Bytes (bv_unsigned inputLength - txConsumed outcome)) ∗
        altFlAllocatorObject (bv_unsigned (argv !!! 1%nat)) (bv_unsigned context) ∗
        altFlVtable ∗
        altFlHeap ∗
        ziskExtraParamsAddress ↦ₘ∗ txScratchAfter outcome ∗
        bv_unsigned (argv !!! 0%nat) ↦ₘ∗ txResultBytes outcome ∗
        txAccessListReturnedHeap outcome ∗
        ⌜txAccessListAllows
           (txAccessListCallArgs argv sp (BV 64 0) inputEndBits txAccessListNoSaved context inputPointer
              inputLength input scratchBefore) outcome⌝ ∗
        True)))%I.

(* Inside the sealed interface the public spec is this template, so a proof
   of the template is a proof of the public spec. *)
Lemma txAccessListCallSpecCorrectFrom `{!islaG Sigma} `{!threadG} (code : iProp Sigma) (entry : Z) :
  (⊢ code -∗ instr_body entry txAccessListCallSpecDefinition) ->
  ⊢ code -∗ instr_body entry txAccessListCallSpecDefinition.
Proof. exact id. Qed.
