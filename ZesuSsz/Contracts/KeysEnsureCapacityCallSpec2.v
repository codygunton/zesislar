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
Require Export ZesuSsz.Contracts.KeysEnsureCapacityContract.
Open Scope Z_scope.
Open Scope stdpp_scope.

(* The contract arguments of a call: a0 = list, a1 = allocator object, a2 =
   requested capacity (argv), the stack pointer and return address of the
   call, the callee-saved registers it preserves, and the owned memory
   values. *)
Definition keysEnsureCapacityCallArgs (argv : list (bv 64)) (sp ret inputEnd : bv 64)
    (saved : ArrayListCalleeSaved) (context : Z) (state : ArrayListState)
    (scratchBefore : list byte) : EnsureCapacityArgs :=
  {| ensureListPointer := argv !!! 0%nat;
     ensureAllocatorPointer := argv !!! 1%nat;
     ensureAllocatorContext := context;
     ensureList := state;
     ensureRequested := argv !!! 2%nat;
     ensureScratchBefore := scratchBefore;
     ensureStackPointer := sp;
     ensureInputEnd := inputEnd;
     ensureReturnAddress := ret;
     ensureSaved := saved |}.

(* The arguments of the outcome relation and the scratch image: they read
   only the list state, the request and the scratch bytes. *)
Definition keysEnsureCapacityOutcomeArgs (requested : bv 64) (state : ArrayListState)
    (scratchBefore : list byte) : EnsureCapacityArgs :=
  keysEnsureCapacityCallArgs [BV 64 0; BV 64 0; requested] (BV 64 0) (BV 64 0) (BV 64 0)
    {| savedX8 := BV 64 0; savedX9 := BV 64 0; savedX18 := BV 64 0;
       savedX19 := BV 64 0; savedX20 := BV 64 0; savedX21 := BV 64 0;
       savedX22 := BV 64 0; savedX23 := BV 64 0; savedX24 := BV 64 0;
       savedX25 := BV 64 0; savedX26 := BV 64 0; savedX27 := BV 64 0 |}
    0 state scratchBefore.

(* The domain of keysEnsureCapacityDomain without its stack and
   return-address conjuncts, which machine_call states. Sealed in the
   interface as keysEnsureCapacityCallDomain. *)
Definition keysEnsureCapacityBoundaryDomain (argv : list (bv 64)) (context : Z)
    (state : ArrayListState) (scratchBefore : list byte) : Prop :=
  arrayListWellFormed keysElementBytes state /\
  arrayListRamRange (bv_unsigned (argv !!! 0%nat)) arrayListHeaderSize /\
  (8 | bv_unsigned (argv !!! 0%nat)) /\
  arrayListRamRange (bv_unsigned (argv !!! 1%nat)) arrayListAllocatorSize /\
  (8 | bv_unsigned (argv !!! 1%nat)) /\
  0 <= context < 2 ^ 64 /\
  bv_unsigned (argv !!! 2%nat) < keysEnsureCapacityMaxRequest /\
  Z.of_nat (length scratchBefore) = arrayListScratchSize.

(* The outcome relation keysEnsureCapacityAllows. Sealed in the interface as
   keysEnsureCapacityCallAllows. *)
Definition keysEnsureCapacityBoundaryAllows (requested : bv 64) (state : ArrayListState)
    (outcome : EnsureCapacityOutcome) : Prop :=
  keysEnsureCapacityAllows (keysEnsureCapacityOutcomeArgs requested state []) outcome.

(* The memcpy scratch word after the call (keysEnsureCapacityScratchAfter). *)
Definition keysEnsureCapacityBoundaryScratch (requested : bv 64) (state : ArrayListState)
    (scratchBefore : list byte) (outcome : EnsureCapacityOutcome) : list byte :=
  keysEnsureCapacityScratchAfter (keysEnsureCapacityOutcomeArgs requested state scratchBefore)
    outcome.

(* The template of keysEnsureCapacity's public call spec:
   KeysEnsureCapacityContractCorrect (KeysEnsureCapacityContract.v) in the
   machine_call shape; the returned x10 (rets !!! 0) is the outcome code.
   Callers never import this module: the public spec
   keysEnsureCapacityCallSpec2 is rendered from this body in
   ZesuSsz/Interfaces/KeysEnsureCapacity.v (tools/block/render_interfaces.py,
   registry ZesuSsz/Contracts/proved_functions.json).
   Compliance/KeysEnsureCapacityCallSpec2.v derives this template from that
   theorem. *)
Definition keysEnsureCapacityCallSpecDefinition `{!islaG Sigma} `{!threadG} : iProp Sigma :=
  (machine_call decodeItemCallMap keysEnsureCapacityStackBytes
    (fun argv sp RET =>
      ∃ (inputEndBits : bv 64) (context : Z) (state : ArrayListState)
        (scratchBefore : list byte),
      "zisk_input_end" ↦ᵣ RVal_Bits inputEndBits ∗
      reg_col [(KindReg "zisk_free_input", BitsShape 64)] ∗
      bv_unsigned (argv !!! 0%nat) ↦ₘ∗ arrayListHeaderBytes state ∗
      arrayListBuffer keysElementBytes keysLog2Alignment state ∗
      ziskExtraParamsAddress ↦ₘ∗ scratchBefore ∗
      altFlAllocatorObject (bv_unsigned (argv !!! 1%nat)) context ∗
      altFlVtable ∗
      altFlHeap ∗
      ⌜keysEnsureCapacityBoundaryDomain argv context state scratchBefore⌝ ∗
      RET (fun rets =>
        ∃ outcome : EnsureCapacityOutcome,
        "zisk_input_end" ↦ᵣ RVal_Bits inputEndBits ∗
        reg_col [(KindReg "zisk_free_input", BitsShape 64)] ∗
        bv_unsigned (argv !!! 0%nat) ↦ₘ∗ arrayListHeaderBytes (ensureListAfter outcome) ∗
        arrayListBuffer keysElementBytes keysLog2Alignment (ensureListAfter outcome) ∗
        ziskExtraParamsAddress ↦ₘ∗
          keysEnsureCapacityBoundaryScratch (argv !!! 2%nat) state scratchBefore outcome ∗
        altFlAllocatorObject (bv_unsigned (argv !!! 1%nat)) context ∗
        altFlVtable ∗
        altFlHeap ∗
        ⌜keysEnsureCapacityBoundaryAllows (argv !!! 2%nat) state outcome⌝ ∗
        ⌜bv_unsigned (rets !!! 0%nat) = arrayListOutcomeCode (ensureKind outcome)⌝ ∗
        True)))%I.

(* Inside the sealed interface the public spec is this template, so a proof
   of the template is a proof of the public spec. *)
Lemma keysEnsureCapacityCallSpecCorrectFrom `{!islaG Sigma} `{!threadG} (code : iProp Sigma) (entry : Z) :
  (⊢ code -∗ instr_body entry keysEnsureCapacityCallSpecDefinition) ->
  ⊢ code -∗ instr_body entry keysEnsureCapacityCallSpecDefinition.
Proof. exact id. Qed.

(* ---- Interface lemmas (registry rows of keysEnsureCapacity). ---- *)

(* The caller states the domain; the sealed domain follows. *)
Lemma keysEnsureCapacityDomainIntro (argv : list (bv 64)) (context : Z)
    (state : ArrayListState) (scratchBefore : list byte) :
  keysEnsureCapacityBoundaryDomain argv context state scratchBefore ->
  keysEnsureCapacityBoundaryDomain argv context state scratchBefore.
Proof. exact id. Qed.

(* What a caller needs after the call: the list stays well formed with its
   length and items; success leaves room for the request; OutOfMemory keeps
   the list. *)
Lemma keysEnsureCapacityAllowsFacts (requested : bv 64) (state : ArrayListState)
    (outcome : EnsureCapacityOutcome) :
  keysEnsureCapacityBoundaryAllows requested state outcome ->
  arrayListWellFormed keysElementBytes (ensureListAfter outcome) /\
  arrayListLength (ensureListAfter outcome) = arrayListLength state /\
  arrayListItems (ensureListAfter outcome) = arrayListItems state /\
  (ensureKind outcome = arrayListSuccess ->
     bv_unsigned requested <= arrayListCapacity (ensureListAfter outcome)) /\
  (ensureKind outcome = arrayListOutOfMemory -> ensureListAfter outcome = state).
Proof.
  unfold keysEnsureCapacityBoundaryAllows, keysEnsureCapacityAllows,
    keysEnsureCapacityOutcomeArgs, keysEnsureCapacityCallArgs, arrayListGrownCapacity.
  cbn [ensureList ensureRequested lookup_total list_lookup_total].
  pose proof (bv_unsigned_in_range _ requested) as Hr.
  intros [Hwf Hcase]. split; [exact Hwf|].
  destruct (bv_unsigned requested <=? arrayListCapacity state) eqn:Hle.
  - apply Z.leb_le in Hle. destruct Hcase as [_ Hs]. rewrite Hs.
    split_and!; intros; try reflexivity; lia.
  - apply Z.leb_gt in Hle.
    destruct (ensureKind outcome) eqn:Hk.
    + destruct Hcase as (Hl & Hc & Hi). split_and!; intros; try assumption; try discriminate.
      rewrite Hc. pose proof (Z.div_pos (bv_unsigned requested) 2). lia.
    + rewrite Hcase. split_and!; intros; try reflexivity; discriminate.
Qed.

Lemma keysEnsureCapacityAllowsLink (requested : bv 64) (state : ArrayListState)
    (outcome : EnsureCapacityOutcome) :
  keysEnsureCapacityBoundaryAllows requested state outcome ->
  keysEnsureCapacityBoundaryAllows requested state outcome.
Proof. exact id. Qed.
