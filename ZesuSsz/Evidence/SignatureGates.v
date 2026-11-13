From Coq Require Import Lists.List ZArith.ZArith.
From stdpp Require Import bitvector.definitions.
From Ltac2 Require Import Ltac2.
Require Import SailStdpp.MachineWord.
Require Import isla.riscv64.riscv64.
Require Import EvmSailRlp.evm_rlp_types.
Require Import ZesuSsz.Compliance.EvmSailAdapter.
Require Import ZesuSsz.Compliance.RlpInputBounds.
Require Import ZesuSsz.Compliance.SailRun.
Require Import ZesuSsz.Compliance.KnownBugs.
Require Import ZesuSsz.Contracts.RlpDecodeItem.
Require Import ZesuSsz.Contracts.RlpDecodeItemContract.
Require Import ZesuSsz.Contracts.RlpDecodeItemSchema.
Require Import ZesuSsz.Contracts.ParentHeaderLevel1.
Require Import ZesuSsz.Contracts.ParentHeaderRequiredFields.
Require Import ZesuSsz.Contracts.ParentHeaderRung2.
Require Import ZesuSsz.Contracts.ParentHeaderMemcpyService.
Require Import ZesuSsz.Contracts.DecodeItemSelected.
Require Import ZesuSsz.Contracts.NextUint64Selected.
Require Import InstrSpecs.Lookup.
Require Import ZesuSsz.Contracts.SelectedCodeLookup.
Require Import ZesuSsz.Contracts.ParentHeaderContract.
Require Import ZesuSsz.Contracts.AbiBytes.
Require Import ZesuSsz.Contracts.ZiskRuntime.
Require Import ZesuSsz.Contracts.DecodeItemCallData.
Require Import ZesuSsz.Automation2.Calls.
Require Import ZesuSsz.Stock.Closure.index_nextUint64.
Require Import ZesuSsz.Stock.Closure.index_decodeItem.
Require Import ZesuSsz.Stock.Closure.index_memcpyStub.
Require Import ZesuMachineMap.Machine.
Require Import InstrSpecs.Machine.
Require Import ZesuSsz.Contracts.Level1.
Require Import ZesuSsz.Contracts.ParentHeaderRootFacts.
Require Import ZesuSsz.Stock.Closure.index_decodeParentHeader.
Require Import ZesuSsz.Evidence.SignatureAxiomAllowlist.

Open Scope Z_scope.
Import ListNotations.

Declare ML Module "zesu-signature-gates.plugin".

Ltac2 @ external exact_axioms : constr -> constr list -> unit :=
  "zesu-signature-gates.plugin" "exact_axioms".

(* A closed control theorem tests the type and axiom gates. *)
Definition ReviewedControlType : Prop :=
  forall bytes : list nat, bytes = bytes.

Theorem reviewed_control : ReviewedControlType.
Proof. unfold ReviewedControlType; intros; reflexivity. Qed.

Check (@reviewed_control : ReviewedControlType).
Print Assumptions reviewed_control.
Ltac2 Eval exact_axioms 'reviewed_control (approved_library_axioms ()).

Definition ReviewedRlpItemType : Type :=
  forall base len : Z, list byte -> RlpCursor base len ->
  SailOutcome
    ({full_len & {content_len & RlpFieldRef base full_len content_len}}%type) -> Prop.

Definition ReviewedRlpHeaderType : Type :=
  forall base len : Z, list byte -> StatelessInputSliceFields base len ->
  SailOutcome (bool * source_pointer * Z) -> Prop.

Definition ReviewedRlpNodeType : Type :=
  forall base len : Z, list byte -> StatelessInputSliceFields base len ->
  SailOutcome
    ({source_len & {source_off & RlpCursor source_off source_len}}%type) -> Prop.

Definition ReviewedParentHeaderFieldsType : Type :=
  forall base len : Z, list byte -> StatelessInputSliceFields base len ->
  parent_header_field_cursor -> ParentHeaderFields ->
  SailOutcome ParentHeaderFields -> Prop.

Check (@ReferenceRlpItem : ReviewedRlpItemType).
Check (@ReferenceRlpHeader : ReviewedRlpHeaderType).
Check (@ReferenceRlpNode : ReviewedRlpNodeType).
Check (@ReferenceParentHeaderFields : ReviewedParentHeaderFieldsType).

(* Definition equality pins the input domain, generated action, initialized
   register state, evaluator, and complete outcome relation. *)
Definition ReviewedRlpItemRelation {base len : Z}
    (bytes : list byte) (cursor : RlpCursor base len)
    (outcome : SailOutcome
      ({full_len & {content_len & RlpFieldRef base full_len content_len}}%type))
    : Prop :=
  validInputSlice bytes base len = true /\
  runRlpDecodeItem bytes cursor = outcome.

Definition ReviewedRlpHeaderRelation {base len : Z}
    (bytes : list byte) (cursor : StatelessInputSliceFields base len)
    (outcome : SailOutcome (bool * source_pointer * Z)) : Prop :=
  validInputSlice bytes base len = true /\
  runRlpRefHdr bytes cursor = outcome.

Definition ReviewedRlpNodeRelation {base len : Z}
    (bytes : list byte) (node : StatelessInputSliceFields base len)
    (outcome : SailOutcome
      ({source_len & {source_off & RlpCursor source_off source_len}}%type))
    : Prop :=
  validInputSlice bytes base len = true /\
  runRlpNodeCursor bytes node = outcome.

Definition ReviewedParentHeaderFieldsRelation {base len : Z}
    (bytes : list byte) (cursor : StatelessInputSliceFields base len)
    (fieldIndex : parent_header_field_cursor) (fields : ParentHeaderFields)
    (outcome : SailOutcome ParentHeaderFields) : Prop :=
  validInputSlice bytes base len = true /\
  0 <= parent_header_field_cursor_value fieldIndex <= 19 /\
  runParentHeaderFields bytes cursor fieldIndex fields = outcome.

Check (eq_refl : @ReferenceRlpItem = @ReviewedRlpItemRelation).
Check (eq_refl : @ReferenceRlpHeader = @ReviewedRlpHeaderRelation).
Check (eq_refl : @ReferenceRlpNode = @ReviewedRlpNodeRelation).
Check (eq_refl : @ReferenceParentHeaderFields =
                  @ReviewedParentHeaderFieldsRelation).

Print Assumptions ReferenceRlpItem.
Print Assumptions ReferenceRlpHeader.
Print Assumptions ReferenceRlpNode.
Print Assumptions ReferenceParentHeaderFields.
Ltac2 Eval exact_axioms 'ReferenceRlpItem (approved_library_axioms ()).
Ltac2 Eval exact_axioms 'ReferenceRlpHeader (approved_library_axioms ()).
Ltac2 Eval exact_axioms 'ReferenceRlpNode (approved_library_axioms ()).
Ltac2 Eval exact_axioms 'ReferenceParentHeaderFields (approved_library_axioms ()).

Definition ReviewedEncodeResultType : Type :=
  Z -> list byte -> list byte -> list byte -> candidateItem -> Prop.
Definition ReviewedRelateItemType : Type :=
  forall base len : Z, Z -> list byte -> list byte -> list byte ->
  SailItemOutcome base len -> Prop.

Check (@encodeResult : ReviewedEncodeResultType).
Check (@relateItem : ReviewedRelateItemType).
Check (@intendedValidRlpClassHeaderFits :
  forall input, intendedValidRlpClass input -> headerFits input).
Print Assumptions intendedValidRlpClassHeaderFits.
Ltac2 Eval exact_axioms 'intendedValidRlpClassHeaderFits
  (approved_library_axioms ()).

Check (@decodeItemAllowsC1B : DecodeItemArgs -> DecodeItemOutcome -> Prop).
Check (eq_refl : decodeItemAllowsC1B = decodeItemAllows C1BResult).
Check (eq_refl : knownBugs = [RlpLongLengthWrap]).

Definition ReviewedDecodeMeaningModuloKnownBugs
    (args : DecodeItemArgs) (after : DecodeItemOutcome) : Prop :=
  decodeItemAllows C1BResult args after /\
  (decodeItemSailResult args after \/
   exists bug, List.In bug knownBugs /\ decodeItemBugApplies bug args after).

Check (@DecodeMeaningModuloKnownBugs :
  DecodeItemArgs -> DecodeItemOutcome -> Prop).
Check (eq_refl : DecodeMeaningModuloKnownBugs =
                 ReviewedDecodeMeaningModuloKnownBugs).
Check (@decodeItemWrapWitness :
  candidateDecodeItem decodeItemWrapWitnessInput =
    candidateSuccess false 9 (word64Modulus - 9) /\
  binaryWrapCase 9 (word64Modulus - 9) 0 /\
  ~ headerFits decodeItemWrapWitnessInput).
Print Assumptions decodeItemWrapWitness.
Ltac2 Eval exact_axioms 'decodeItemWrapWitness (approved_library_axioms ()).

Definition ReviewedParentHeaderMeaningModuloKnownBugs
    (args : ParentHeaderCall) (result : list byte) : Prop :=
  parentHeaderDomain args /\
  (parentHeaderSuccessAgreement args.(headerInputBytes) result \/
   parentHeaderRejectionAgreement args.(headerInputBytes) result).

Check (@ParentHeaderMeaningModuloKnownBugs :
  ParentHeaderCall -> list byte -> Prop).
Check (eq_refl : ParentHeaderMeaningModuloKnownBugs =
                 ReviewedParentHeaderMeaningModuloKnownBugs).
Check (@emptyParentListMissesRequired :
  parentHeaderMissingRequiredField [Z_to_bv 8 192]).
Print Assumptions emptyParentListMissesRequired.
Ltac2 Eval exact_axioms 'emptyParentListMissesRequired
  (approved_library_axioms ()).

Local Open Scope stdpp_scope.

Definition ReviewedStockZiskPermissions : ZiskRuntimePermissions :=
  {| ziskReadableSection := fun address count =>
       Exists (fun section =>
         sectionReadable section = true /\
         sectionBase section <= address /\
         address + count <= sectionEnd section)
         (mapPopulatedSections defaultMap);
     ziskWritableSection := fun address count =>
       mapRamBase defaultMap <= address /\
       address + count <= machineRamEnd defaultMap /\
       Forall (fun section =>
         sectionWritable section = true \/
         address + count <= sectionBase section \/
         sectionEnd section <= address)
         (mapPopulatedSections defaultMap) |}.

Definition ReviewedParentHeaderMemcpyDomain (destination : Z) : Prop :=
  ziskMemcpyRange destination 80 /\
  ziskReadableSection ReviewedStockZiskPermissions 0x80114fb8 80 /\
  ziskWritableSection ReviewedStockZiskPermissions destination 80 /\
  ziskWritableSection ReviewedStockZiskPermissions 0xa0400f00 8.

Definition ReviewedMemcpyCallSpec2 `{!islaG Sigma} `{!threadG} : iProp Sigma :=
  (machine_call decodeItemCallMap 0
    (fun argv sp RET =>
      ∃ (source scratch : list byte),
      ⌜bv_unsigned (argv !!! 1%nat) = 0x80114fb8⌝ ∗
      ⌜bv_unsigned (argv !!! 2%nat) = 80⌝ ∗
      ⌜ReviewedParentHeaderMemcpyDomain (bv_unsigned (argv !!! 0%nat))⌝ ∗
      reg_col [(KindReg "zisk_input_end", BitsShape 64);
               (KindReg "zisk_free_input", BitsShape 64)] ∗
      0x80114fb8 ↦ₘ∗ source ∗
      bv_unsigned (argv !!! 0%nat) ↦ₘ? 80 ∗
      0xa0400f00 ↦ₘ∗ scratch ∗
      ⌜Z.of_nat (length source) = 80⌝ ∗
      ⌜length scratch = 8%nat⌝ ∗
      RET (fun _ =>
        reg_col [(KindReg "zisk_input_end", BitsShape 64);
                 (KindReg "zisk_free_input", BitsShape 64)] ∗
        0x80114fb8 ↦ₘ∗ source ∗
        bv_unsigned (argv !!! 0%nat) ↦ₘ∗ source ∗
        0xa0400f00 ↦ₘ∗ word64Bytes 80 ∗
        True)))%I.

Definition ReviewedMemcpyCallPremise `{!islaG Sigma} `{!threadG} :
    iProp Sigma :=
  (□ instr_pre memcpyCsrPc ReviewedMemcpyCallSpec2)%I.

Check (eq_refl : stockZiskPermissions = ReviewedStockZiskPermissions).
Check (eq_refl : parentHeaderMemcpyDomain = ReviewedParentHeaderMemcpyDomain).
Check (eq_refl : @memcpyCallSpec2 = @ReviewedMemcpyCallSpec2).
Check (eq_refl : @memcpyCallPremise = @ReviewedMemcpyCallPremise).
Check (eq_refl : parentHeaderMemcpyLength = 80%Z).
Check (eq_refl : parentHeaderMemcpySource = 0x80114fb8%Z).

Definition ReviewedNextUint64SelectedCode `{!islaG Sigma} `{!threadG} :
    iProp Sigma :=
  instr_lookup_resources
    (selectedCodeLookup ZesuSsz.Stock.Closure.index_nextUint64.instr_map).

Definition ReviewedParentHeaderSelectedCode `{!islaG Sigma} `{!threadG} :
    iProp Sigma :=
  instr_lookup_resources
    (selectedCodeLookup ZesuSsz.Stock.Closure.index_decodeParentHeader.instr_map).

Definition ReviewedParentHeaderContractCode `{!islaG Sigma} `{!threadG} :
    iProp Sigma :=
  (ReviewedParentHeaderSelectedCode ∗ nextUint64SelectedCode ∗
   decodeItemSelectedCode ∗ memcpyCallPremise)%I.

(* The meaning conjuncts of decodeParentHeader's Level 1 contract. *)
Definition ReviewedParentHeaderAllows
    (args : ParentHeaderCall) (outcome : ParentHeaderOutcome) : Prop :=
  ParentHeaderMeaningModuloKnownBugs args outcome.(headerResultBytes) /\
  List.length outcome.(headerAfterFrame) = 400%nat /\
  match outcome.(headerExitPath) with
  | ParentHeaderDirect => True
  | ParentHeaderMemcpyTail =>
      outcome.(headerResultBytes) = args.(headerMemcpySourceBefore)
  end.

Check (eq_refl : @nextUint64SelectedCode = @ReviewedNextUint64SelectedCode).
Check (eq_refl : @parentHeaderSelectedCode =
                 @ReviewedParentHeaderSelectedCode).
Check (eq_refl : @parentHeaderContractCode =
                 @ReviewedParentHeaderContractCode).
Check (eq_refl : parentHeaderAllows = ReviewedParentHeaderAllows).
Check (@NextUint64SelectedCorrect : Prop).

(* The complete reviewed statement of the parent contract. *)
Definition ReviewedParentHeaderCall (args : ParentHeaderArgs) : ParentHeaderCall :=
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

Definition ReviewedParentHeaderArgsWellFormed (args : ParentHeaderArgs) : Prop :=
  Z.of_nat (length (parentHeaderInputBytes args)) =
    bv_unsigned (parentHeaderInputLength args) /\
  length (parentHeaderMemcpySourceBefore args) = 80%nat /\
  length (parentHeaderMemcpyScratchBefore args) = 8%nat /\
  parentHeaderError80 (parentHeaderMemcpySourceBefore args) /\
  0x40000000 <= bv_unsigned (parentHeaderInputPointer args) /\
  bv_unsigned (parentHeaderInputPointer args) +
    bv_unsigned (parentHeaderInputLength args) <= 0x80000000 /\
  bv_unsigned (parentHeaderInputPointer args) +
    bv_unsigned (parentHeaderInputLength args) <=
    bv_unsigned (parentHeaderInputEnd args) /\
  0xa0000000 <= bv_unsigned (parentHeaderResultPointer args) /\
  bv_unsigned (parentHeaderResultPointer args) + 80 <= 0xc0000000 /\
  0xa0000000 + 400 + 112 <= bv_unsigned (parentHeaderStackPointer args) /\
  bv_unsigned (parentHeaderStackPointer args) < 0xc0000000 /\
  bv_unsigned (parentHeaderStackPointer args) mod 16 = 0 /\
  bv_unsigned (parentHeaderReturnAddress args) mod 4 = 0 /\
  separateRanges (bv_unsigned (parentHeaderResultPointer args)) 80
    (bv_unsigned (parentHeaderStackPointer args) - 400) 400 /\
  separateRanges (bv_unsigned (parentHeaderResultPointer args)) 80
    (bv_unsigned (parentHeaderStackPointer args) - 400 - 112) 112 /\
  separateRanges 0xa0400f00 8
    (bv_unsigned (parentHeaderResultPointer args)) 80 /\
  separateRanges 0xa0400f00 8
    (bv_unsigned (parentHeaderStackPointer args) - 400) 400 /\
  separateRanges 0xa0400f00 8
    (bv_unsigned (parentHeaderStackPointer args) - 400 - 112) 112.

Definition ReviewedParentHeaderSysRegs (args : ParentHeaderArgs) :
    list (reg_kind * valu_shape) :=
  map (fun '(r, shape) =>
    (r, if decide (r = KindReg "zisk_input_end")
        then ExactShape (RVal_Bits (parentHeaderInputEnd args))
        else shape)) zesu_sys_regs.

Definition ReviewedParentHeaderEntryResources `{!islaG Sigma} `{!threadG}
    (args : ParentHeaderArgs) : iProp Sigma :=
  (∃ (x5 x6 x7 x13 x14 x15 x16 x17 x28 x29 x30 x31 : bv 64),
   reg_col (ReviewedParentHeaderSysRegs args) ∗
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
   bv_unsigned (parentHeaderResultPointer args) ↦ₘ? 80 ∗
   (bv_unsigned (parentHeaderStackPointer args) - 400) ↦ₘ? 400 ∗
   (bv_unsigned (parentHeaderStackPointer args) - 400 - 112) ↦ₘ? 112 ∗
   0x80114fb8 ↦ₘ∗ parentHeaderMemcpySourceBefore args ∗
   0xa0400f00 ↦ₘ∗ parentHeaderMemcpyScratchBefore args ∗
   ⌜ReviewedParentHeaderArgsWellFormed args⌝ ∗ True)%I.

Definition ReviewedParentHeaderScratchAfter (args : ParentHeaderArgs)
    (path : ParentHeaderExitPath) : list byte :=
  match path with
  | ParentHeaderDirect => parentHeaderMemcpyScratchBefore args
  | ParentHeaderMemcpyTail => word64Bytes 80
  end.

Definition ReviewedParentHeaderExitSysRegs (args : ParentHeaderArgs)
    (path : ParentHeaderExitPath) : list (reg_kind * valu_shape) :=
  match path with
  | ParentHeaderDirect => ReviewedParentHeaderSysRegs args
  | ParentHeaderMemcpyTail => zesu_sys_regs
  end.

Definition ReviewedParentHeaderExitResources `{!islaG Sigma} `{!threadG}
    (args : ParentHeaderArgs) (outcome : ParentHeaderOutcome) : iProp Sigma :=
  (∃ (x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 : bv 64),
   reg_col (ReviewedParentHeaderExitSysRegs args outcome.(headerExitPath)) ∗
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
   (bv_unsigned (parentHeaderStackPointer args) - 400) ↦ₘ∗
     outcome.(headerAfterFrame) ∗
   (bv_unsigned (parentHeaderStackPointer args) - 400 - 112) ↦ₘ? 112 ∗
   0x80114fb8 ↦ₘ∗ parentHeaderMemcpySourceBefore args ∗
   0xa0400f00 ↦ₘ∗
     ReviewedParentHeaderScratchAfter args outcome.(headerExitPath) ∗ True)%I.

Definition ReviewedParentHeaderContractResources `{!islaG Sigma} `{!threadG}
    (returnAddress : Z) :
    IslarisContractResources ParentHeaderArgs ParentHeaderOutcome :=
  {| islarisCode := ReviewedParentHeaderContractCode;
     islarisEntry := fun args =>
       (⌜bv_unsigned (parentHeaderReturnAddress args) = returnAddress⌝ ∗
        ReviewedParentHeaderEntryResources args)%I;
     islarisExit := ReviewedParentHeaderExitResources |}.

Definition ReviewedParentHeaderContractModel (returnAddress : Z) :
    IslarisContractModel ParentHeaderArgs ParentHeaderOutcome :=
  {| islarisContractAllows := fun args outcome =>
       bv_unsigned (parentHeaderReturnAddress args) = returnAddress /\
       ReviewedParentHeaderAllows (ReviewedParentHeaderCall args) outcome;
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
       @ReviewedParentHeaderContractResources Sigma HG HT returnAddress |}.

Definition ReviewedParentHeaderContractCorrect : Prop :=
  forall returnAddress,
    IslarisContractCorrect 0x800d5cb8 returnAddress
      (ReviewedParentHeaderContractModel returnAddress).

Check (eq_refl : parentHeaderCall = ReviewedParentHeaderCall).
Check (eq_refl : parentHeaderArgsWellFormed = ReviewedParentHeaderArgsWellFormed).
Check (eq_refl : parentHeaderExitSysRegs = ReviewedParentHeaderExitSysRegs).
Check (eq_refl : ParentHeaderContractCorrect = ReviewedParentHeaderContractCorrect).
