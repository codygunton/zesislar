From Coq Require Import List ZArith.
From stdpp Require Import bitvector.definitions.
Require Import EvmSailRlp.evm_rlp_types.
Require Import isla.riscv64.riscv64.
Require Import InstrSpecs.Machine.
Require Import InstrSpecs.Lookup.
Require Import ZesuSsz.Contracts.SelectedCodeLookup.
Require Import ZesuSsz.Stock.Closure.index_decodeParentHeader.
Require Import ZesuSsz.Stock.Closure.index_memcpyStub.
Require Import ZesuSsz.Stock.Closure.index_nextUint64.
Require Import ZesuSsz.Contracts.AbiBytes.
Require Import ZesuSsz.Contracts.RlpDecodeItem.
Require Import ZesuSsz.Contracts.DecodeItemSelected.
Require Import ZesuSsz.Contracts.Level1.
Require Import ZesuSsz.Contracts.NextUint64Selected.
Require Import ZesuSsz.Contracts.ParentHeader.
Require Import ZesuSsz.Contracts.ParentHeaderLevel1.
Require Import ZesuSsz.Contracts.ParentHeaderMemcpyService.
Require Import ZesuSsz.Contracts.ParentHeaderRootFacts.
Require Import ZesuSsz.Contracts.ParentHeaderRung2.
Require Import ZesuSsz.Contracts.ZiskRuntime.

Open Scope Z_scope.

(* The Level 1 contract of rlp_decode.decodeParentHeader (entry 0x800d5cb8).
   The frame is 400 bytes. Below it lie the callee frames: decodeItem uses
   16 bytes, nextUint64 96 and its own decodeItem call 16, so 112 bytes.
   The input lies in the ZisK input buffer; the stack and the result in RAM. *)
Notation parentHeaderCalleeBytes := ((112) : Z) (only parsing).
Notation parentHeaderResultSize := ((80) : Z) (only parsing).
Notation parentHeaderScratchSize := ((8) : Z) (only parsing).
Notation parentHeaderRamLow := ((0xa0000000) : Z) (only parsing).
Notation parentHeaderRamHigh := ((0xc0000000) : Z) (only parsing).
Notation parentHeaderInputLow := ((0x40000000) : Z) (only parsing).
Notation parentHeaderInputHigh := ((0x80000000) : Z) (only parsing).

Inductive ParentHeaderExitPath :=
| ParentHeaderDirect
| ParentHeaderMemcpyTail.

Record ParentHeaderOutcome := {
  headerExitPath : ParentHeaderExitPath;
  headerResultBytes : list byte;
  headerAfterFrame : list byte
}.

(* The meaning conjuncts, unchanged from the former ParentHeaderSelected.v. *)
Definition parentHeaderAllows
    (args : ParentHeaderCall) (outcome : ParentHeaderOutcome) : Prop :=
  ParentHeaderMeaningModuloKnownBugs args outcome.(headerResultBytes) /\
  List.length outcome.(headerAfterFrame) = 400%nat /\
  match outcome.(headerExitPath) with
  | ParentHeaderDirect => True
  | ParentHeaderMemcpyTail =>
      outcome.(headerResultBytes) = args.(headerMemcpySourceBefore)
  end.

(* Register quantities are the register values themselves (F44). *)
Record ParentHeaderArgs := {
  parentHeaderResultPointer : bv 64;
  parentHeaderInputPointer : bv 64;
  parentHeaderInputLength : bv 64;
  parentHeaderInputBytes : list byte;
  parentHeaderInputEnd : bv 64;
  parentHeaderStackPointer : bv 64;
  parentHeaderReturnAddress : bv 64;
  parentHeaderSavedX8 : bv 64; parentHeaderSavedX9 : bv 64;
  parentHeaderSavedX18 : bv 64; parentHeaderSavedX19 : bv 64;
  parentHeaderSavedX20 : bv 64; parentHeaderSavedX21 : bv 64;
  parentHeaderSavedX22 : bv 64; parentHeaderSavedX23 : bv 64;
  parentHeaderSavedX24 : bv 64; parentHeaderSavedX25 : bv 64;
  parentHeaderSavedX26 : bv 64; parentHeaderSavedX27 : bv 64;
  parentHeaderMemcpySourceBefore : list byte;
  parentHeaderMemcpyScratchBefore : list byte
}.

(* The meaning reads the input and the layout. The frame is uninitialized
   at entry, so the call records no frame bytes. *)
Definition parentHeaderCall (args : ParentHeaderArgs) : ParentHeaderCall :=
  {| headerInputPointer := bv_unsigned (parentHeaderInputPointer args);
     headerInputBytes := parentHeaderInputBytes args;
     headerResultPointer := bv_unsigned (parentHeaderResultPointer args);
     headerStackPointer := bv_unsigned (parentHeaderStackPointer args);
     headerReturnAddress := bv_unsigned (parentHeaderReturnAddress args);
     headerSavedS0 := parentHeaderSavedX8 args;
     headerSavedS1 := parentHeaderSavedX9 args;
     headerSavedS2 := parentHeaderSavedX18 args;
     headerSavedS3 := parentHeaderSavedX19 args;
     headerSavedS4 := parentHeaderSavedX20 args;
     headerSavedS5 := parentHeaderSavedX21 args;
     headerSavedS6 := parentHeaderSavedX22 args;
     headerSavedS7 := parentHeaderSavedX23 args;
     headerSavedS8 := parentHeaderSavedX24 args;
     headerBeforeFrame := [];
     headerMemcpySourceBefore := parentHeaderMemcpySourceBefore args;
     headerMemcpyScratchBefore := parentHeaderMemcpyScratchBefore args |}.

(* Each machine bound is a separate conjunct on bv_unsigned of a register
   value, with a constant on the other side (F44). *)
Definition parentHeaderArgsWellFormed (args : ParentHeaderArgs) : Prop :=
  Z.of_nat (length (parentHeaderInputBytes args)) =
    bv_unsigned (parentHeaderInputLength args) /\
  length (parentHeaderMemcpySourceBefore args) = 80%nat /\
  length (parentHeaderMemcpyScratchBefore args) = 8%nat /\
  parentHeaderError80 (parentHeaderMemcpySourceBefore args) /\
  parentHeaderInputLow <= bv_unsigned (parentHeaderInputPointer args) /\
  bv_unsigned (parentHeaderInputPointer args) +
    bv_unsigned (parentHeaderInputLength args) <= parentHeaderInputHigh /\
  bv_unsigned (parentHeaderInputPointer args) +
    bv_unsigned (parentHeaderInputLength args) <=
    bv_unsigned (parentHeaderInputEnd args) /\
  parentHeaderRamLow <= bv_unsigned (parentHeaderResultPointer args) /\
  bv_unsigned (parentHeaderResultPointer args) + parentHeaderResultSize <=
    parentHeaderRamHigh /\
  parentHeaderRamLow + parentHeaderStackBytes + parentHeaderCalleeBytes <=
    bv_unsigned (parentHeaderStackPointer args) /\
  bv_unsigned (parentHeaderStackPointer args) < parentHeaderRamHigh /\
  bv_unsigned (parentHeaderStackPointer args) mod 16 = 0 /\
  bv_unsigned (parentHeaderReturnAddress args) mod 4 = 0 /\
  separateRanges (bv_unsigned (parentHeaderResultPointer args)) parentHeaderResultSize
    (bv_unsigned (parentHeaderStackPointer args) - parentHeaderStackBytes)
    parentHeaderStackBytes /\
  separateRanges (bv_unsigned (parentHeaderResultPointer args)) parentHeaderResultSize
    (bv_unsigned (parentHeaderStackPointer args) - parentHeaderStackBytes -
       parentHeaderCalleeBytes) parentHeaderCalleeBytes /\
  separateRanges ziskExtraParamsAddress parentHeaderScratchSize
    (bv_unsigned (parentHeaderResultPointer args)) parentHeaderResultSize /\
  separateRanges ziskExtraParamsAddress parentHeaderScratchSize
    (bv_unsigned (parentHeaderStackPointer args) - parentHeaderStackBytes)
    parentHeaderStackBytes /\
  separateRanges ziskExtraParamsAddress parentHeaderScratchSize
    (bv_unsigned (parentHeaderStackPointer args) - parentHeaderStackBytes -
       parentHeaderCalleeBytes) parentHeaderCalleeBytes.

(* zisk_input_end holds the input end that the decodeItem calls need. *)
Definition parentHeaderSysRegs (args : ParentHeaderArgs) :
    list (reg_kind * valu_shape) :=
  map (fun '(r, shape) =>
    (r, if decide (r = KindReg "zisk_input_end")
        then ExactShape (RVal_Bits (parentHeaderInputEnd args))
        else shape)) zesu_sys_regs.

Lemma parentHeaderSysRegs_exact (args : ParentHeaderArgs) :
  parentHeaderSysRegs args = (machine_static_sys_regs defaultMap ++
    [(KindReg "zisk_input_end",
      ExactShape (RVal_Bits (parentHeaderInputEnd args)));
     (KindReg "zisk_free_input", BitsShape 64)])%list.
Proof. reflexivity. Qed.

(* The selected code is the own map only (F55). Callee code enters through
   the table-level bridge: nextUint64CallSpec2 and decodeItemCallSpec2 from
   the callee code below, memcpyCallSpec2 from the runtime premise (F57). *)
Definition parentHeaderSelectedCode `{!islaG Sigma} `{!threadG} : iProp Sigma :=
  instr_lookup_resources
    (selectedCodeLookup ZesuSsz.Stock.Closure.index_decodeParentHeader.instr_map).

Definition parentHeaderContractCode `{!islaG Sigma} `{!threadG} : iProp Sigma :=
  (parentHeaderSelectedCode ∗ nextUint64SelectedCode ∗ decodeItemSelectedCode ∗
   memcpyCallPremise)%I.

Definition parentHeaderEntryResources `{!islaG Sigma} `{!threadG}
    (args : ParentHeaderArgs) : iProp Sigma :=
  (∃ (x5 x6 x7 x13 x14 x15 x16 x17 x28 x29 x30 x31 : bv 64),
   reg_col (parentHeaderSysRegs args) ∗
   "x1" ↦ᵣ RVal_Bits (parentHeaderReturnAddress args) ∗
   "x2" ↦ᵣ RVal_Bits (parentHeaderStackPointer args) ∗
   "x5" ↦ᵣ RVal_Bits x5 ∗ "x6" ↦ᵣ RVal_Bits x6 ∗ "x7" ↦ᵣ RVal_Bits x7 ∗
   "x8" ↦ᵣ RVal_Bits (parentHeaderSavedX8 args) ∗
   "x9" ↦ᵣ RVal_Bits (parentHeaderSavedX9 args) ∗
   "x10" ↦ᵣ RVal_Bits (parentHeaderResultPointer args) ∗
   "x11" ↦ᵣ RVal_Bits (parentHeaderInputPointer args) ∗
   "x12" ↦ᵣ RVal_Bits (parentHeaderInputLength args) ∗
   "x13" ↦ᵣ RVal_Bits x13 ∗ "x14" ↦ᵣ RVal_Bits x14 ∗ "x15" ↦ᵣ RVal_Bits x15 ∗
   "x16" ↦ᵣ RVal_Bits x16 ∗ "x17" ↦ᵣ RVal_Bits x17 ∗
   "x18" ↦ᵣ RVal_Bits (parentHeaderSavedX18 args) ∗
   "x19" ↦ᵣ RVal_Bits (parentHeaderSavedX19 args) ∗
   "x20" ↦ᵣ RVal_Bits (parentHeaderSavedX20 args) ∗
   "x21" ↦ᵣ RVal_Bits (parentHeaderSavedX21 args) ∗
   "x22" ↦ᵣ RVal_Bits (parentHeaderSavedX22 args) ∗
   "x23" ↦ᵣ RVal_Bits (parentHeaderSavedX23 args) ∗
   "x24" ↦ᵣ RVal_Bits (parentHeaderSavedX24 args) ∗
   "x25" ↦ᵣ RVal_Bits (parentHeaderSavedX25 args) ∗
   "x26" ↦ᵣ RVal_Bits (parentHeaderSavedX26 args) ∗
   "x27" ↦ᵣ RVal_Bits (parentHeaderSavedX27 args) ∗
   "x28" ↦ᵣ RVal_Bits x28 ∗ "x29" ↦ᵣ RVal_Bits x29 ∗
   "x30" ↦ᵣ RVal_Bits x30 ∗ "x31" ↦ᵣ RVal_Bits x31 ∗
   bv_unsigned (parentHeaderInputPointer args) ↦ₘ∗ parentHeaderInputBytes args ∗
   bv_unsigned (parentHeaderResultPointer args) ↦ₘ? parentHeaderResultSize ∗
   (bv_unsigned (parentHeaderStackPointer args) - parentHeaderStackBytes) ↦ₘ?
     parentHeaderStackBytes ∗
   (bv_unsigned (parentHeaderStackPointer args) - parentHeaderStackBytes -
      parentHeaderCalleeBytes) ↦ₘ? parentHeaderCalleeBytes ∗
   parentHeaderMemcpySource ↦ₘ∗ parentHeaderMemcpySourceBefore args ∗
   ziskExtraParamsAddress ↦ₘ∗ parentHeaderMemcpyScratchBefore args ∗
   ⌜parentHeaderArgsWellFormed args⌝ ∗ True)%I.

Definition parentHeaderScratchAfter (args : ParentHeaderArgs)
    (path : ParentHeaderExitPath) : list byte :=
  match path with
  | ParentHeaderDirect => parentHeaderMemcpyScratchBefore args
  | ParentHeaderMemcpyTail => word64Bytes parentHeaderMemcpyLength
  end.

(* The ABI returns the caller-saved registers, x1 among them, with arbitrary
   values: the memcpy tail returns through the caller's ra itself. It
   preserves the callee-saved registers and the stack pointer. *)
Definition parentHeaderExitResources `{!islaG Sigma} `{!threadG}
    (args : ParentHeaderArgs) (outcome : ParentHeaderOutcome) : iProp Sigma :=
  (∃ (x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 : bv 64),
   reg_col (parentHeaderSysRegs args) ∗
   "x1" ↦ᵣ RVal_Bits x1 ∗
   "x2" ↦ᵣ RVal_Bits (parentHeaderStackPointer args) ∗
   "x5" ↦ᵣ RVal_Bits x5 ∗ "x6" ↦ᵣ RVal_Bits x6 ∗ "x7" ↦ᵣ RVal_Bits x7 ∗
   "x8" ↦ᵣ RVal_Bits (parentHeaderSavedX8 args) ∗
   "x9" ↦ᵣ RVal_Bits (parentHeaderSavedX9 args) ∗
   "x10" ↦ᵣ RVal_Bits x10 ∗ "x11" ↦ᵣ RVal_Bits x11 ∗ "x12" ↦ᵣ RVal_Bits x12 ∗
   "x13" ↦ᵣ RVal_Bits x13 ∗ "x14" ↦ᵣ RVal_Bits x14 ∗ "x15" ↦ᵣ RVal_Bits x15 ∗
   "x16" ↦ᵣ RVal_Bits x16 ∗ "x17" ↦ᵣ RVal_Bits x17 ∗
   "x18" ↦ᵣ RVal_Bits (parentHeaderSavedX18 args) ∗
   "x19" ↦ᵣ RVal_Bits (parentHeaderSavedX19 args) ∗
   "x20" ↦ᵣ RVal_Bits (parentHeaderSavedX20 args) ∗
   "x21" ↦ᵣ RVal_Bits (parentHeaderSavedX21 args) ∗
   "x22" ↦ᵣ RVal_Bits (parentHeaderSavedX22 args) ∗
   "x23" ↦ᵣ RVal_Bits (parentHeaderSavedX23 args) ∗
   "x24" ↦ᵣ RVal_Bits (parentHeaderSavedX24 args) ∗
   "x25" ↦ᵣ RVal_Bits (parentHeaderSavedX25 args) ∗
   "x26" ↦ᵣ RVal_Bits (parentHeaderSavedX26 args) ∗
   "x27" ↦ᵣ RVal_Bits (parentHeaderSavedX27 args) ∗
   "x28" ↦ᵣ RVal_Bits x28 ∗ "x29" ↦ᵣ RVal_Bits x29 ∗
   "x30" ↦ᵣ RVal_Bits x30 ∗ "x31" ↦ᵣ RVal_Bits x31 ∗
   bv_unsigned (parentHeaderInputPointer args) ↦ₘ∗ parentHeaderInputBytes args ∗
   bv_unsigned (parentHeaderResultPointer args) ↦ₘ∗ outcome.(headerResultBytes) ∗
   (bv_unsigned (parentHeaderStackPointer args) - parentHeaderStackBytes) ↦ₘ∗
     outcome.(headerAfterFrame) ∗
   (bv_unsigned (parentHeaderStackPointer args) - parentHeaderStackBytes -
      parentHeaderCalleeBytes) ↦ₘ? parentHeaderCalleeBytes ∗
   parentHeaderMemcpySource ↦ₘ∗ parentHeaderMemcpySourceBefore args ∗
   ziskExtraParamsAddress ↦ₘ∗
     parentHeaderScratchAfter args outcome.(headerExitPath) ∗ True)%I.

Definition parentHeaderContractResources `{!islaG Sigma} `{!threadG}
    (returnAddress : Z) :
    IslarisContractResources ParentHeaderArgs ParentHeaderOutcome :=
  {| islarisCode := parentHeaderContractCode;
     islarisEntry := fun args =>
       (⌜bv_unsigned (parentHeaderReturnAddress args) = returnAddress⌝ ∗
        parentHeaderEntryResources args)%I;
     islarisExit := parentHeaderExitResources |}.

Definition parentHeaderContractModel (returnAddress : Z) :
    IslarisContractModel ParentHeaderArgs ParentHeaderOutcome :=
  {| islarisContractAllows := fun args outcome =>
       bv_unsigned (parentHeaderReturnAddress args) = returnAddress /\
       parentHeaderAllows (parentHeaderCall args) outcome;
     islarisContractStep := fun source target =>
       ZesuSsz.Stock.Closure.index_decodeParentHeader.decodeParentHeader_cfg_step
         source target \/
       ZesuSsz.Stock.Closure.index_nextUint64.nextUint64_cfg_step
         source target \/
       ZesuSsz.Stock.Closure.index_decodeItem.decodeItem_cfg_step
         source target \/
       ZesuSsz.Stock.Closure.index_memcpyStub.memcpyStub_cfg_step
         source target;
     islarisContractResources := fun Sigma HG HT =>
       @parentHeaderContractResources Sigma HG HT returnAddress |}.

(* This declaration states the native proof objective. It does not prove it. *)
Definition ParentHeaderContractCorrect : Prop :=
  forall returnAddress,
    IslarisContractCorrect decodeParentHeaderEntry returnAddress
      (parentHeaderContractModel returnAddress).

(* The machine domain implies the layout that the meaning conjuncts state. *)
Lemma parentHeaderArgsWellFormed_domain (args : ParentHeaderArgs) :
  parentHeaderArgsWellFormed args -> parentHeaderDomain (parentHeaderCall args).
Proof.
  unfold parentHeaderArgsWellFormed, parentHeaderDomain, parentHeaderEntryLayout,
    parentHeaderCall, separateRanges; cbn.
  pose proof (bv_unsigned_in_range 64 (parentHeaderInputPointer args)).
  pose proof (bv_unsigned_in_range 64 (parentHeaderInputLength args)).
  pose proof (bv_unsigned_in_range 64 (parentHeaderResultPointer args)).
  pose proof (bv_unsigned_in_range 64 (parentHeaderStackPointer args)).
  pose proof (bv_unsigned_in_range 64 (parentHeaderReturnAddress args)).
  unfold bv_modulus in *. cbn in *.
  intros (Hlength & _ & _ & _ & Hlow & Hhigh & _ & Hres & Hresh & Hsp & Hsph & _ & Hra & _).
  rewrite Hlength. lia.
Qed.
