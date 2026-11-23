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
Require Import ZesuSsz.Contracts.Candidates.ParentHeaderDomain.
Require Import ZesuSsz.Contracts.Candidates.ParentHeaderCandidate.
Require Import ZesuSsz.Contracts.ParentHeaderBugTriggers.
Require Import ZesuSsz.Compliance.ProjectionParentHeader.
Require Import ZesuSsz.Generated.Stock.Symbols.
Require Import ZesuSsz.Contracts.AltFlFree.
Require Import ZesuSsz.Contracts.AltFlAllocPremises.
Require Import ZesuSsz.Contracts.ZiskMemcpyPremise.
Require Import ZesuSsz.Contracts.ArrayListContract.
Require Import ZesuSsz.Contracts.KeysToOwnedSliceSelected.
Require Import ZesuSsz.Contracts.EntriesToOwnedSliceSelected.
Require Import ZesuSsz.Contracts.KeysEnsureCapacitySelected.
Require Import ZesuSsz.Contracts.KeysToOwnedSliceContract.
Require Import ZesuSsz.Contracts.EntriesToOwnedSliceContract.
Require Import ZesuSsz.Contracts.KeysEnsureCapacityContract.
Require ZesuSsz.Stock.Closure.index_sliceBytes32.
Require ZesuSsz.Stock.Closure.index_sliceAccessList.
Require ZesuSsz.Stock.Closure.index_ensureTotalCapacity.
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
Check (eq_refl : knownBugs =
  [RlpLongLengthWrap; ParentHeaderMissingRequiredField;
   ParentHeaderTrailingBytes; ParentHeaderSkippedFieldShape;
   ParentHeaderBlobGasUnaligned; RlpUintNonCanonical;
   ParentHeaderUintOver8; ParentHeaderUndecodedFieldRejected;
   ParentHeaderExcessBlobGasAboveLimit; ParentHeaderTrailingItemMalformed]).

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

Check (@candidateParentHeader : list byte -> ParentHeaderCandidate).

Definition ReviewedParentHeaderCandidateResult (bytes result : list byte) : Prop :=
  match candidateParentHeader bytes with
  | candidateHeaderSuccess header => parentHeaderResult80 result header
  | candidateHeaderError => parentHeaderError80 result
  end.

Check (eq_refl : parentHeaderCandidateResult =
                 ReviewedParentHeaderCandidateResult).

Definition ReviewedParentHeaderBugTrigger (bug : KnownBug)
    (bytes : list byte) : bool :=
  match bug with
  | RlpLongLengthWrap => nestedWrapOccursb bytes
  | ParentHeaderMissingRequiredField => missingRequiredFieldb bytes
  | ParentHeaderTrailingBytes => trailingBytesb bytes
  | ParentHeaderSkippedFieldShape => skippedFieldShapeb bytes
  | ParentHeaderBlobGasUnaligned => blobGasUnalignedb bytes
  | RlpUintNonCanonical => uintNonCanonicalb bytes
  | ParentHeaderUintOver8 => uintOver8b bytes
  | ParentHeaderUndecodedFieldRejected => undecodedFieldRejectedb bytes
  | ParentHeaderExcessBlobGasAboveLimit => excessBlobGasAboveLimitb bytes
  | ParentHeaderTrailingItemMalformed => trailingItemMalformedb bytes
  end.

Check (eq_refl : parentHeaderBugTrigger = ReviewedParentHeaderBugTrigger).
Check (@nestedWrapOccursb_spec :
  forall bytes, nestedWrapOccursb bytes = true <-> nestedWrapOccurs bytes).
Print Assumptions nestedWrapOccursb_spec.
Ltac2 Eval exact_axioms 'nestedWrapOccursb_spec (approved_library_axioms ()).

Definition ReviewedParentHeaderSailAgrees (bytes : list byte) : Prop :=
  match candidateParentHeader bytes with
  | candidateHeaderSuccess header =>
      ParentHeaderSuccess bytes (parentHeaderSailNode bytes) header
  | candidateHeaderError =>
      ParentHeaderRejects bytes (parentHeaderSailNode bytes)
  end.

Check (eq_refl : parentHeaderSailAgrees = ReviewedParentHeaderSailAgrees).

Definition ReviewedParentHeaderMeaningModuloKnownBugs
    (args : ParentHeaderCall) (result : list byte) : Prop :=
  parentHeaderDomain args /\
  ReviewedParentHeaderCandidateResult args.(headerInputBytes) result /\
  (ReviewedParentHeaderSailAgrees args.(headerInputBytes) \/
   exists bug, List.In bug knownBugs /\
     ReviewedParentHeaderBugTrigger bug args.(headerInputBytes) = true).

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
Check (eq_refl : memcpyCsrPc = 0x800e06c0%Z).

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

(* The outer header of a decodeParentHeader input fits: a long-length header
   that is complete states a total length below 2^64. *)
Definition ReviewedHeaderFits (bytes : list byte) : Prop :=
  match bytes with
  | [] => True
  | prefix :: rest =>
      let width := longLengthWidth (bv_unsigned prefix) in
      width = 0 \/ Z.of_nat (List.length rest) < width \/
      1 + width + bigEndian (firstn (Z.to_nat width) rest) < 2 ^ 64
  end.

Definition ReviewedParentHeaderArgsWellFormed (args : ParentHeaderArgs) : Prop :=
  Z.of_nat (length (parentHeaderInputBytes args)) =
    bv_unsigned (parentHeaderInputLength args) /\
  length (parentHeaderMemcpySourceBefore args) = 80%nat /\
  length (parentHeaderMemcpyScratchBefore args) = 8%nat /\
  length (replicate 16%nat (BV 8 0)) = 16%nat /\
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
    (bv_unsigned (parentHeaderStackPointer args) - 400 - 112) 112 /\
  ReviewedHeaderFits (parentHeaderInputBytes args).

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
   0x801152b0 ↦ₘ∗ replicate 16%nat (BV 8 0) ∗
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
   0x801152b0 ↦ₘ∗ replicate 16%nat (BV 8 0) ∗
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
Check (eq_refl : headerFits = ReviewedHeaderFits).
Check (eq_refl : parentHeaderExitSysRegs = ReviewedParentHeaderExitSysRegs).
Check (eq_refl : ParentHeaderContractCorrect = ReviewedParentHeaderContractCorrect).

(* allocator and memcpy premises (PR #363) *)
Definition ReviewedAltFlClassBytes (class : Z) : Z := 2 ^ (class + 3).
Definition ReviewedAltFlListHead (lists : list byte) (class : Z) : Z :=
  littleEndian (firstn 8 (skipn (Z.to_nat (8 + 8 * class)) lists)).
Definition ReviewedAltFlChainHead (blocks : list Z) : Z :=
  match blocks with
  | [] => 0
  | block :: _ => block
  end.
Definition ReviewedAltFlChainBlockFacts (blockBytes block : Z) : Prop :=
  mapRamBase defaultMap <= block /\
  block + blockBytes <= machineRamEnd defaultMap /\
  (blockBytes | block).
Fixpoint ReviewedAltFlChain `{!islaG Sigma} `{!threadG}
    (blockBytes head : Z) (blocks : list Z) : iProp Sigma :=
  match blocks with
  | [] => ⌜head = 0⌝
  | block :: rest =>
      ⌜head = block /\ altFlChainBlockFacts blockBytes block⌝ ∗
      block ↦ₘ∗ word64Bytes (altFlChainHead rest) ∗
      (block + 8) ↦ₘ? (blockBytes - 8) ∗
      ReviewedAltFlChain blockBytes (altFlChainHead rest) rest
  end%I.
Definition ReviewedAltFlHeapWellFormed (heap : AltFlHeapState) : Prop :=
  Z.of_nat (length (altFlLists heap)) = freeListsBytes /\
  Z.of_nat (length (altFlChains heap)) = freeListCount /\
  0 <= altFlHeapPos heap <= altFlMaxHeapPos /\
  0 <= altFlHeapTop heap < 2 ^ 64 /\
  (altFlHeapPos heap < altFlHeapTop heap ->
    mapRamBase defaultMap <= altFlHeapPos heap /\
    altFlHeapTop heap <= machineRamEnd defaultMap).
Definition ReviewedAltFlHeapAt `{!islaG Sigma} `{!threadG}
    (heap : AltFlHeapState) : iProp Sigma :=
  (sym_alt_fl_alloc_state ↦ₘ∗ altFlLists heap ∗
   mapHeapPosAddress defaultMap ↦ₘ∗ word64Bytes (altFlHeapPos heap) ∗
   mapHeapTopAddress defaultMap ↦ₘ∗ word64Bytes (altFlHeapTop heap) ∗
   altFlHeapPos heap ↦ₘ? Z.max 0 (altFlHeapTop heap - altFlHeapPos heap) ∗
   ([∗ list] class ↦ blocks ∈ altFlChains heap,
      altFlChain (altFlClassBytes (Z.of_nat class))
        (altFlListHead (altFlLists heap) (Z.of_nat class)) blocks))%I.
Definition ReviewedAltFlHeap `{!islaG Sigma} `{!threadG} : iProp Sigma :=
  (∃ heap : AltFlHeapState, altFlHeapAt heap ∗ ⌜altFlHeapWellFormed heap⌝)%I.
Definition ReviewedAltFlBlockSlack (bytes log2Align : Z) : Z :=
  if bytes =? 0 then 0
  else if freeSizeClass bytes log2Align <? freeListCount
  then altFlClassBytes (freeSizeClass bytes log2Align) - bytes
  else 0.
Definition ReviewedAltFlBlockAlignment (bytes log2Align : Z) : Z :=
  if freeSizeClass bytes log2Align <? freeListCount
  then altFlClassBytes (freeSizeClass bytes log2Align)
  else 2 ^ log2Align.
Definition ReviewedAltFlBlockFacts (pointer bytes log2Align : Z) : Prop :=
  mapRamBase defaultMap <= pointer /\
  pointer + bytes + altFlBlockSlack bytes log2Align <= machineRamEnd defaultMap /\
  (altFlBlockAlignment bytes log2Align | pointer).
Definition ReviewedAltFlBlock `{!islaG Sigma} `{!threadG}
    (pointer bytes log2Align : Z) : iProp Sigma :=
  ((pointer + bytes) ↦ₘ? altFlBlockSlack bytes log2Align ∗
   ⌜bytes <> 0 -> altFlBlockFacts pointer bytes log2Align⌝)%I.
Definition ReviewedAltFlAllocatedBytes (pointer bytes : Z) : Z :=
  if pointer =? 0 then 0 else bytes.
Definition ReviewedAltFlVtableBytes : list byte :=
  word64Bytes sym_alt_fl_alloc_alloc ++ word64Bytes sym_alt_fl_alloc_resize ++
  word64Bytes sym_alt_fl_alloc_remap ++ word64Bytes sym_alt_fl_alloc_free.
Definition ReviewedAltFlVtable `{!islaG Sigma} `{!threadG} : iProp Sigma :=
  (sym_alt_fl_alloc_vtable ↦ₘ∗ altFlVtableBytes)%I.
Definition ReviewedAltFlAllocatorBytes (context : Z) : list byte :=
  word64Bytes context ++ word64Bytes sym_alt_fl_alloc_vtable.
Definition ReviewedAltFlAllocatorObject `{!islaG Sigma} `{!threadG}
    (pointer context : Z) : iProp Sigma :=
  (pointer ↦ₘ∗ altFlAllocatorBytes context)%I.
Definition ReviewedAltFlAllocDomain (bytes log2Align : Z) : Prop :=
  0 < bytes < altFlMaxRequestBytes /\ 0 <= log2Align <= altFlMaxLog2Alignment.
Definition ReviewedAltFlAllocCallSpec `{!islaG Sigma} `{!threadG} : iProp Sigma :=
  (machine_call decodeItemCallMap altFlCallStackBytes
    (fun argv sp RET =>
      ⌜altFlAllocDomain (bv_unsigned (argv !!! 1%nat))
        (bv_unsigned (argv !!! 2%nat))⌝ ∗
      altFlHeap ∗
      RET (fun rets =>
        altFlHeap ∗
        bv_unsigned (rets !!! 0%nat) ↦ₘ?
          altFlAllocatedBytes (bv_unsigned (rets !!! 0%nat))
            (bv_unsigned (argv !!! 1%nat)) ∗
        altFlBlock (bv_unsigned (rets !!! 0%nat))
          (altFlAllocatedBytes (bv_unsigned (rets !!! 0%nat))
            (bv_unsigned (argv !!! 1%nat)))
          (bv_unsigned (argv !!! 2%nat)) ∗
        True)))%I.
Definition ReviewedAltFlRemapCallSpec `{!islaG Sigma} `{!threadG} : iProp Sigma :=
  (machine_call decodeItemCallMap altFlCallStackBytes
    (fun argv sp RET =>
      RET (fun rets => ⌜bv_unsigned (rets !!! 0%nat) = 0⌝ ∗ True)))%I.
Definition ReviewedAltFlFreeDomain (bytes log2Align : Z) : Prop :=
  0 < bytes < altFlMaxRequestBytes /\ 0 <= log2Align <= altFlMaxLog2Alignment.
Definition ReviewedAltFlFreeCallSpec `{!islaG Sigma} `{!threadG} : iProp Sigma :=
  (machine_call decodeItemCallMap altFlCallStackBytes
    (fun argv sp RET =>
      ⌜altFlFreeDomain (bv_unsigned (argv !!! 2%nat))
        (bv_unsigned (argv !!! 3%nat))⌝ ∗
      altFlHeap ∗
      bv_unsigned (argv !!! 1%nat) ↦ₘ? bv_unsigned (argv !!! 2%nat) ∗
      altFlBlock (bv_unsigned (argv !!! 1%nat)) (bv_unsigned (argv !!! 2%nat))
        (bv_unsigned (argv !!! 3%nat)) ∗
      RET (fun _ => altFlHeap ∗ True)))%I.
Definition ReviewedAltFlAllocCallPremise `{!islaG Sigma} `{!threadG} : iProp Sigma :=
  (□ instr_pre sym_alt_fl_alloc_alloc altFlAllocCallSpec)%I.
Definition ReviewedAltFlRemapCallPremise `{!islaG Sigma} `{!threadG} : iProp Sigma :=
  (□ instr_pre sym_alt_fl_alloc_remap altFlRemapCallSpec)%I.
Definition ReviewedAltFlFreeCallPremise `{!islaG Sigma} `{!threadG} : iProp Sigma :=
  (□ instr_pre sym_alt_fl_alloc_free altFlFreeCallSpec)%I.
Definition ReviewedAltFlAllocatorPremises `{!islaG Sigma} `{!threadG} : iProp Sigma :=
  (altFlAllocCallPremise ∗ altFlRemapCallPremise ∗ altFlFreeCallPremise)%I.
Definition ReviewedZiskMemcpyCallDomain (destination source length : Z) : Prop :=
  ziskWord destination /\ ziskWord source /\ ziskWord length /\
  ziskWritableSection stockZiskPermissions ziskExtraParamsAddress 8 /\
  (length <> 0 ->
    ziskMemcpyRange destination length /\
    ziskMemcpyRange source length /\
    ziskWritableSection stockZiskPermissions source length /\
    ziskWritableSection stockZiskPermissions destination length).
Definition ReviewedZiskMemcpyCallSpec `{!islaG Sigma} `{!threadG} : iProp Sigma :=
  (machine_call decodeItemCallMap 0
    (fun argv sp RET =>
      ∃ (inputEndBits : bv 64) (source scratch : list byte),
      "zisk_input_end" ↦ᵣ RVal_Bits inputEndBits ∗
      ⌜ziskMemcpyCallDomain (bv_unsigned (argv !!! 0%nat))
        (bv_unsigned (argv !!! 1%nat)) (bv_unsigned (argv !!! 2%nat))⌝ ∗
      reg_col [(KindReg "zisk_free_input", BitsShape 64)] ∗
      bv_unsigned (argv !!! 1%nat) ↦ₘ∗ source ∗
      bv_unsigned (argv !!! 0%nat) ↦ₘ? bv_unsigned (argv !!! 2%nat) ∗
      ziskExtraParamsAddress ↦ₘ∗ scratch ∗
      ⌜Z.of_nat (length source) = bv_unsigned (argv !!! 2%nat)⌝ ∗
      ⌜length scratch = 8%nat⌝ ∗
      RET (fun _ =>
        "zisk_input_end" ↦ᵣ RVal_Bits inputEndBits ∗
        reg_col [(KindReg "zisk_free_input", BitsShape 64)] ∗
        bv_unsigned (argv !!! 1%nat) ↦ₘ∗ source ∗
        bv_unsigned (argv !!! 0%nat) ↦ₘ∗ source ∗
        ziskExtraParamsAddress ↦ₘ∗ word64Bytes (bv_unsigned (argv !!! 2%nat)) ∗
        True)))%I.
Definition ReviewedZiskMemcpyCallPremise `{!islaG Sigma} `{!threadG} : iProp Sigma :=
  (□ instr_pre sym_memcpy ziskMemcpyCallSpec)%I.
Check (eq_refl : @altFlClassBytes = @ReviewedAltFlClassBytes).
Check (eq_refl : @altFlListHead = @ReviewedAltFlListHead).
Check (eq_refl : @altFlChainHead = @ReviewedAltFlChainHead).
Check (eq_refl : @altFlChainBlockFacts = @ReviewedAltFlChainBlockFacts).
Check (eq_refl : @altFlChain = @ReviewedAltFlChain).
Check (eq_refl : @altFlHeapWellFormed = @ReviewedAltFlHeapWellFormed).
Check (eq_refl : @altFlHeapAt = @ReviewedAltFlHeapAt).
Check (eq_refl : @altFlHeap = @ReviewedAltFlHeap).
Check (eq_refl : @altFlBlockSlack = @ReviewedAltFlBlockSlack).
Check (eq_refl : @altFlBlockAlignment = @ReviewedAltFlBlockAlignment).
Check (eq_refl : @altFlBlockFacts = @ReviewedAltFlBlockFacts).
Check (eq_refl : @altFlBlock = @ReviewedAltFlBlock).
Check (eq_refl : @altFlAllocatedBytes = @ReviewedAltFlAllocatedBytes).
Check (eq_refl : @altFlVtableBytes = @ReviewedAltFlVtableBytes).
Check (eq_refl : @altFlVtable = @ReviewedAltFlVtable).
Check (eq_refl : @altFlAllocatorBytes = @ReviewedAltFlAllocatorBytes).
Check (eq_refl : @altFlAllocatorObject = @ReviewedAltFlAllocatorObject).
Check (eq_refl : @altFlAllocDomain = @ReviewedAltFlAllocDomain).
Check (eq_refl : @altFlAllocCallSpec = @ReviewedAltFlAllocCallSpec).
Check (eq_refl : @altFlRemapCallSpec = @ReviewedAltFlRemapCallSpec).
Check (eq_refl : @altFlFreeDomain = @ReviewedAltFlFreeDomain).
Check (eq_refl : @altFlFreeCallSpec = @ReviewedAltFlFreeCallSpec).
Check (eq_refl : @altFlAllocCallPremise = @ReviewedAltFlAllocCallPremise).
Check (eq_refl : @altFlRemapCallPremise = @ReviewedAltFlRemapCallPremise).
Check (eq_refl : @altFlFreeCallPremise = @ReviewedAltFlFreeCallPremise).
Check (eq_refl : @altFlAllocatorPremises = @ReviewedAltFlAllocatorPremises).
Check (eq_refl : @ziskMemcpyCallDomain = @ReviewedZiskMemcpyCallDomain).
Check (eq_refl : @ziskMemcpyCallSpec = @ReviewedZiskMemcpyCallSpec).
Check (eq_refl : @ziskMemcpyCallPremise = @ReviewedZiskMemcpyCallPremise).

(* array-list regions (PR #363) *)
Definition ReviewedKeysToOwnedSliceSelectedCode `{!islaG Sigma} `{!threadG} : iProp Sigma :=
  instr_lookup_resources
    (selectedCodeLookup ZesuSsz.Stock.Closure.index_sliceBytes32.instr_map).
Definition ReviewedEntriesToOwnedSliceSelectedCode `{!islaG Sigma} `{!threadG} : iProp Sigma :=
  instr_lookup_resources
    (selectedCodeLookup ZesuSsz.Stock.Closure.index_sliceAccessList.instr_map).
Definition ReviewedKeysEnsureCapacitySelectedCode `{!islaG Sigma} `{!threadG} : iProp Sigma :=
  instr_lookup_resources
    (selectedCodeLookup ZesuSsz.Stock.Closure.index_ensureTotalCapacity.instr_map).
Definition ReviewedArrayListEmpty (pointer : Z) : ArrayListState :=
  {| arrayListPointer := pointer; arrayListLength := 0;
     arrayListCapacity := 0; arrayListItems := [] |}.
Definition ReviewedArrayListHeaderBytes (state : ArrayListState) : list byte :=
  word64Bytes (arrayListPointer state) ++ word64Bytes (arrayListLength state) ++
  word64Bytes (arrayListCapacity state).
Definition ReviewedArrayListRamRange (pointer bytes : Z) : Prop :=
  mapRamBase defaultMap <= pointer /\ pointer + bytes <= machineRamEnd defaultMap.
Definition ReviewedArrayListWellFormed (elementBytes : Z) (state : ArrayListState) : Prop :=
  0 <= arrayListLength state <= arrayListCapacity state /\
  Z.of_nat (length (arrayListItems state)) = arrayListLength state * elementBytes /\
  0 < arrayListPointer state < 2 ^ 64 /\
  (0 < arrayListCapacity state ->
    arrayListRamRange (arrayListPointer state)
      (arrayListCapacity state * elementBytes)).
Definition ReviewedArrayListBuffer `{!islaG Sigma} `{!threadG}
    (elementBytes log2Align : Z) (state : ArrayListState) : iProp Sigma :=
  (arrayListPointer state ↦ₘ∗ arrayListItems state ∗
   (arrayListPointer state + arrayListLength state * elementBytes) ↦ₘ?
     ((arrayListCapacity state - arrayListLength state) * elementBytes) ∗
   altFlBlock (arrayListPointer state)
     (arrayListCapacity state * elementBytes) log2Align)%I.
Definition ReviewedArrayListOutcomeCode (kind : ArrayListOutcomeKind) : Z :=
  match kind with
  | arrayListSuccess => 0
  | arrayListOutOfMemory => arrayListOutOfMemoryCode
  end.
Definition ReviewedArrayListSavedRegisters `{!islaG Sigma} `{!threadG}
    (saved : ArrayListCalleeSaved) : iProp Sigma :=
  ("x8" ↦ᵣ RVal_Bits (savedX8 saved) ∗ "x9" ↦ᵣ RVal_Bits (savedX9 saved) ∗
   "x18" ↦ᵣ RVal_Bits (savedX18 saved) ∗ "x19" ↦ᵣ RVal_Bits (savedX19 saved) ∗
   "x20" ↦ᵣ RVal_Bits (savedX20 saved) ∗ "x21" ↦ᵣ RVal_Bits (savedX21 saved) ∗
   "x22" ↦ᵣ RVal_Bits (savedX22 saved) ∗ "x23" ↦ᵣ RVal_Bits (savedX23 saved) ∗
   "x24" ↦ᵣ RVal_Bits (savedX24 saved) ∗ "x25" ↦ᵣ RVal_Bits (savedX25 saved) ∗
   "x26" ↦ᵣ RVal_Bits (savedX26 saved) ∗ "x27" ↦ᵣ RVal_Bits (savedX27 saved))%I.
Definition ReviewedArrayListSysRegs (inputEnd : bv 64) : list (reg_kind * valu_shape) :=
  machine_static_sys_regs defaultMap ++
  [(KindReg "zisk_input_end", ExactShape (RVal_Bits inputEnd));
   (KindReg "zisk_free_input", BitsShape 64)].
Definition ReviewedArrayListStackLayout (stackPointer stackBytes : Z) : Prop :=
  (16 | stackPointer) /\
  mapRamBase defaultMap <= stackPointer - stackBytes /\
  stackPointer <= machineRamEnd defaultMap.
Definition ReviewedArrayListResultImage (before : list byte) (pointer length : Z) :
    list byte :=
  word64Bytes pointer ++ word64Bytes length ++ firstn 2 (word64Bytes 0) ++
  skipn 18 before.
Definition ReviewedArrayListErrorImage (before : list byte) (code : Z) : list byte :=
  firstn 16 before ++ firstn 2 (word64Bytes code) ++ skipn 18 before.
Definition ReviewedToOwnedSliceDomain (elementBytes : Z) (args : ToOwnedSliceArgs) :
    Prop :=
  arrayListWellFormed elementBytes (toOwnedList args) /\
  arrayListRamRange (bv_unsigned (toOwnedResultPointer args)) arrayListResultSize /\
  (8 | bv_unsigned (toOwnedResultPointer args)) /\
  arrayListRamRange (bv_unsigned (toOwnedListPointer args)) arrayListHeaderSize /\
  (8 | bv_unsigned (toOwnedListPointer args)) /\
  arrayListRamRange (bv_unsigned (toOwnedAllocatorPointer args)) arrayListAllocatorSize /\
  (8 | bv_unsigned (toOwnedAllocatorPointer args)) /\
  Z.of_nat (length (toOwnedResultBefore args)) = arrayListResultSize /\
  Z.of_nat (length (toOwnedScratchBefore args)) = arrayListScratchSize /\
  0 <= toOwnedAllocatorContext args < 2 ^ 64 /\
  arrayListStackLayout (bv_unsigned (toOwnedStackPointer args))
    arrayListToOwnedSliceStackBytes /\
  (4 | bv_unsigned (toOwnedReturnAddress args)).
Definition ReviewedToOwnedSliceAllows (elementBytes emptyPointer : Z)
    (args : ToOwnedSliceArgs) (outcome : ToOwnedSliceOutcome) : Prop :=
  let state := toOwnedList args in
  let before := toOwnedResultBefore args in
  arrayListWellFormed elementBytes (toOwnedListAfter outcome) /\
  arrayListWellFormed elementBytes (toOwnedSlice outcome) /\
  arrayListCapacity (toOwnedSlice outcome) =
    arrayListLength (toOwnedSlice outcome) /\
  (if arrayListLength state =? 0 then
     toOwnedKind outcome = arrayListSuccess /\
     toOwnedListAfter outcome = arrayListEmpty emptyPointer /\
     toOwnedSlice outcome = arrayListEmpty (arrayListPointer state) /\
     toOwnedResultAfter outcome =
       arrayListResultImage before (arrayListPointer state) 0
   else
     match toOwnedKind outcome with
     | arrayListSuccess =>
         toOwnedListAfter outcome = arrayListEmpty (arrayListPointer state) /\
         arrayListLength (toOwnedSlice outcome) = arrayListLength state /\
         arrayListItems (toOwnedSlice outcome) = arrayListItems state /\
         toOwnedResultAfter outcome =
           arrayListResultImage before
             (arrayListPointer (toOwnedSlice outcome)) (arrayListLength state)
     | arrayListOutOfMemory =>
         toOwnedListAfter outcome = state /\
         toOwnedSlice outcome = arrayListEmpty emptyPointer /\
         toOwnedResultAfter outcome =
           arrayListErrorImage before arrayListOutOfMemoryCode
     end).
Definition ReviewedToOwnedSliceScratchAfter (elementBytes : Z) (args : ToOwnedSliceArgs)
    (outcome : ToOwnedSliceOutcome) : list byte :=
  if arrayListLength (toOwnedList args) =? 0 then toOwnedScratchBefore args
  else
    match toOwnedKind outcome with
    | arrayListSuccess =>
        word64Bytes (arrayListLength (toOwnedList args) * elementBytes)
    | arrayListOutOfMemory => toOwnedScratchBefore args
    end.
Definition ReviewedToOwnedSliceEntry `{!islaG Sigma} `{!threadG}
    (elementBytes log2Align : Z) (args : ToOwnedSliceArgs) : iProp Sigma :=
  (∃ (x5 x6 x7 x13 x14 x15 x16 x17 x28 x29 x30 x31 : bv 64),
   reg_col (arrayListSysRegs (toOwnedInputEnd args)) ∗
   "x1" ↦ᵣ RVal_Bits (toOwnedReturnAddress args) ∗
   "x2" ↦ᵣ RVal_Bits (toOwnedStackPointer args) ∗
   "x5" ↦ᵣ RVal_Bits x5 ∗ "x6" ↦ᵣ RVal_Bits x6 ∗ "x7" ↦ᵣ RVal_Bits x7 ∗
   "x10" ↦ᵣ RVal_Bits (toOwnedResultPointer args) ∗
   "x11" ↦ᵣ RVal_Bits (toOwnedListPointer args) ∗
   "x12" ↦ᵣ RVal_Bits (toOwnedAllocatorPointer args) ∗
   "x13" ↦ᵣ RVal_Bits x13 ∗ "x14" ↦ᵣ RVal_Bits x14 ∗ "x15" ↦ᵣ RVal_Bits x15 ∗
   "x16" ↦ᵣ RVal_Bits x16 ∗ "x17" ↦ᵣ RVal_Bits x17 ∗
   "x28" ↦ᵣ RVal_Bits x28 ∗ "x29" ↦ᵣ RVal_Bits x29 ∗
   "x30" ↦ᵣ RVal_Bits x30 ∗ "x31" ↦ᵣ RVal_Bits x31 ∗
   arrayListSavedRegisters (toOwnedSaved args) ∗
   bv_unsigned (toOwnedListPointer args) ↦ₘ∗ arrayListHeaderBytes (toOwnedList args) ∗
   arrayListBuffer elementBytes log2Align (toOwnedList args) ∗
   bv_unsigned (toOwnedResultPointer args) ↦ₘ∗ toOwnedResultBefore args ∗
   ziskExtraParamsAddress ↦ₘ∗ toOwnedScratchBefore args ∗
   altFlAllocatorObject (bv_unsigned (toOwnedAllocatorPointer args))
     (toOwnedAllocatorContext args) ∗
   altFlVtable ∗
   altFlHeap ∗
   (bv_unsigned (toOwnedStackPointer args) - arrayListToOwnedSliceStackBytes) ↦ₘ?
     arrayListToOwnedSliceStackBytes ∗
   ⌜toOwnedSliceDomain elementBytes args⌝ ∗ True)%I.
Definition ReviewedToOwnedSliceExit `{!islaG Sigma} `{!threadG}
    (elementBytes log2Align : Z) (args : ToOwnedSliceArgs)
    (outcome : ToOwnedSliceOutcome) : iProp Sigma :=
  (∃ (x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 : bv 64),
   reg_col (arrayListSysRegs (toOwnedInputEnd args)) ∗
   "x1" ↦ᵣ RVal_Bits (toOwnedReturnAddress args) ∗
   "x2" ↦ᵣ RVal_Bits (toOwnedStackPointer args) ∗
   "x5" ↦ᵣ RVal_Bits x5 ∗ "x6" ↦ᵣ RVal_Bits x6 ∗ "x7" ↦ᵣ RVal_Bits x7 ∗
   "x10" ↦ᵣ RVal_Bits x10 ∗ "x11" ↦ᵣ RVal_Bits x11 ∗ "x12" ↦ᵣ RVal_Bits x12 ∗
   "x13" ↦ᵣ RVal_Bits x13 ∗ "x14" ↦ᵣ RVal_Bits x14 ∗ "x15" ↦ᵣ RVal_Bits x15 ∗
   "x16" ↦ᵣ RVal_Bits x16 ∗ "x17" ↦ᵣ RVal_Bits x17 ∗
   "x28" ↦ᵣ RVal_Bits x28 ∗ "x29" ↦ᵣ RVal_Bits x29 ∗
   "x30" ↦ᵣ RVal_Bits x30 ∗ "x31" ↦ᵣ RVal_Bits x31 ∗
   arrayListSavedRegisters (toOwnedSaved args) ∗
   bv_unsigned (toOwnedListPointer args) ↦ₘ∗ arrayListHeaderBytes (toOwnedListAfter outcome) ∗
   arrayListBuffer elementBytes log2Align (toOwnedListAfter outcome) ∗
   arrayListBuffer elementBytes log2Align (toOwnedSlice outcome) ∗
   bv_unsigned (toOwnedResultPointer args) ↦ₘ∗ toOwnedResultAfter outcome ∗
   ziskExtraParamsAddress ↦ₘ∗
     toOwnedSliceScratchAfter elementBytes args outcome ∗
   altFlAllocatorObject (bv_unsigned (toOwnedAllocatorPointer args))
     (toOwnedAllocatorContext args) ∗
   altFlVtable ∗
   altFlHeap ∗
   (bv_unsigned (toOwnedStackPointer args) - arrayListToOwnedSliceStackBytes) ↦ₘ?
     arrayListToOwnedSliceStackBytes ∗ True)%I.
Definition ReviewedToOwnedSliceResources `{!islaG Sigma} `{!threadG}
    (code : iProp Sigma) (elementBytes log2Align returnAddress : Z) :
    IslarisContractResources ToOwnedSliceArgs ToOwnedSliceOutcome :=
  {| islarisCode := code;
     islarisEntry := fun args =>
       (⌜bv_unsigned (toOwnedReturnAddress args) = returnAddress⌝ ∗
        toOwnedSliceEntry elementBytes log2Align args)%I;
     islarisExit := toOwnedSliceExit elementBytes log2Align |}.
Definition ReviewedToOwnedSliceModel
    (code : forall (Sigma : gFunctors), islaG Sigma -> threadG -> iProp Sigma)
    (step : Z -> Z -> Prop)
    (elementBytes log2Align emptyPointer returnAddress : Z) :
    IslarisContractModel ToOwnedSliceArgs ToOwnedSliceOutcome :=
  {| islarisContractAllows := fun args outcome =>
       bv_unsigned (toOwnedReturnAddress args) = returnAddress /\
       toOwnedSliceDomain elementBytes args /\
       toOwnedSliceAllows elementBytes emptyPointer args outcome;
     islarisContractStep := step;
     islarisContractResources := fun Sigma HG HT =>
       @toOwnedSliceResources Sigma HG HT (code Sigma HG HT)
         elementBytes log2Align returnAddress |}.
Definition ReviewedKeysToOwnedSliceContractCode `{!islaG Sigma} `{!threadG} : iProp Sigma :=
  (keysToOwnedSliceSelectedCode ∗ altFlAllocatorPremises ∗ ziskMemcpyCallPremise)%I.
Definition ReviewedKeysToOwnedSliceContractModel (returnAddress : Z) :
    IslarisContractModel ToOwnedSliceArgs ToOwnedSliceOutcome :=
  toOwnedSliceModel (fun Sigma HG HT => @keysToOwnedSliceContractCode Sigma HG HT)
    ZesuSsz.Stock.Closure.index_sliceBytes32.sliceBytes32_cfg_step
    keysElementBytes keysLog2Alignment keysEmptyPointer returnAddress.
Definition ReviewedKeysToOwnedSliceContractCorrect : Prop :=
  forall returnAddress,
    IslarisContractCorrect sym_array_list_Aligned_32_u8_null_toOwnedSlice returnAddress
      (keysToOwnedSliceContractModel returnAddress).
Definition ReviewedEntriesToOwnedSliceContractCode `{!islaG Sigma} `{!threadG} : iProp Sigma :=
  (entriesToOwnedSliceSelectedCode ∗ altFlAllocatorPremises ∗ ziskMemcpyCallPremise)%I.
Definition ReviewedEntriesToOwnedSliceContractModel (returnAddress : Z) :
    IslarisContractModel ToOwnedSliceArgs ToOwnedSliceOutcome :=
  toOwnedSliceModel (fun Sigma HG HT => @entriesToOwnedSliceContractCode Sigma HG HT)
    ZesuSsz.Stock.Closure.index_sliceAccessList.sliceAccessList_cfg_step
    entriesElementBytes entriesLog2Alignment entriesEmptyPointer returnAddress.
Definition ReviewedEntriesToOwnedSliceContractCorrect : Prop :=
  forall returnAddress,
    IslarisContractCorrect sym_array_list_Aligned_input_AccessListEntry_null_toOwnedSlice returnAddress
      (entriesToOwnedSliceContractModel returnAddress).
Definition ReviewedArrayListGrownCapacity (requested : Z) : Z :=
  requested + requested / 2 + 2.
Definition ReviewedKeysEnsureCapacityDomain (args : EnsureCapacityArgs) : Prop :=
  arrayListWellFormed keysElementBytes (ensureList args) /\
  arrayListRamRange (bv_unsigned (ensureListPointer args)) arrayListHeaderSize /\
  (8 | bv_unsigned (ensureListPointer args)) /\
  arrayListRamRange (bv_unsigned (ensureAllocatorPointer args)) arrayListAllocatorSize /\
  (8 | bv_unsigned (ensureAllocatorPointer args)) /\
  0 <= ensureAllocatorContext args < 2 ^ 64 /\
  bv_unsigned (ensureRequested args) < keysEnsureCapacityMaxRequest /\
  Z.of_nat (length (ensureScratchBefore args)) = arrayListScratchSize /\
  arrayListStackLayout (bv_unsigned (ensureStackPointer args)) keysEnsureCapacityStackBytes /\
  (4 | bv_unsigned (ensureReturnAddress args)).
Definition ReviewedKeysEnsureCapacityAllows (args : EnsureCapacityArgs)
    (outcome : EnsureCapacityOutcome) : Prop :=
  let state := ensureList args in
  arrayListWellFormed keysElementBytes (ensureListAfter outcome) /\
  (if bv_unsigned (ensureRequested args) <=? arrayListCapacity state then
     ensureKind outcome = arrayListSuccess /\ ensureListAfter outcome = state
   else
     match ensureKind outcome with
     | arrayListSuccess =>
         arrayListLength (ensureListAfter outcome) = arrayListLength state /\
         arrayListCapacity (ensureListAfter outcome) =
           arrayListGrownCapacity (bv_unsigned (ensureRequested args)) /\
         arrayListItems (ensureListAfter outcome) = arrayListItems state
     | arrayListOutOfMemory => ensureListAfter outcome = state
     end).
Definition ReviewedKeysEnsureCapacityScratchAfter (args : EnsureCapacityArgs)
    (outcome : EnsureCapacityOutcome) : list byte :=
  if bv_unsigned (ensureRequested args) <=? arrayListCapacity (ensureList args)
  then ensureScratchBefore args
  else
    match ensureKind outcome with
    | arrayListSuccess =>
        word64Bytes (arrayListLength (ensureList args) * keysElementBytes)
    | arrayListOutOfMemory => ensureScratchBefore args
    end.
Definition ReviewedKeysEnsureCapacityEntry `{!islaG Sigma} `{!threadG}
    (args : EnsureCapacityArgs) : iProp Sigma :=
  (∃ (x5 x6 x7 x13 x14 x15 x16 x17 x28 x29 x30 x31 : bv 64),
   reg_col (arrayListSysRegs (ensureInputEnd args)) ∗
   "x1" ↦ᵣ RVal_Bits (ensureReturnAddress args) ∗
   "x2" ↦ᵣ RVal_Bits (ensureStackPointer args) ∗
   "x5" ↦ᵣ RVal_Bits x5 ∗ "x6" ↦ᵣ RVal_Bits x6 ∗ "x7" ↦ᵣ RVal_Bits x7 ∗
   "x10" ↦ᵣ RVal_Bits (ensureListPointer args) ∗
   "x11" ↦ᵣ RVal_Bits (ensureAllocatorPointer args) ∗
   "x12" ↦ᵣ RVal_Bits (ensureRequested args) ∗
   "x13" ↦ᵣ RVal_Bits x13 ∗ "x14" ↦ᵣ RVal_Bits x14 ∗ "x15" ↦ᵣ RVal_Bits x15 ∗
   "x16" ↦ᵣ RVal_Bits x16 ∗ "x17" ↦ᵣ RVal_Bits x17 ∗
   "x28" ↦ᵣ RVal_Bits x28 ∗ "x29" ↦ᵣ RVal_Bits x29 ∗
   "x30" ↦ᵣ RVal_Bits x30 ∗ "x31" ↦ᵣ RVal_Bits x31 ∗
   arrayListSavedRegisters (ensureSaved args) ∗
   bv_unsigned (ensureListPointer args) ↦ₘ∗ arrayListHeaderBytes (ensureList args) ∗
   arrayListBuffer keysElementBytes keysLog2Alignment (ensureList args) ∗
   ziskExtraParamsAddress ↦ₘ∗ ensureScratchBefore args ∗
   altFlAllocatorObject (bv_unsigned (ensureAllocatorPointer args))
     (ensureAllocatorContext args) ∗
   altFlVtable ∗
   altFlHeap ∗
   (bv_unsigned (ensureStackPointer args) - keysEnsureCapacityStackBytes) ↦ₘ?
     keysEnsureCapacityStackBytes ∗
   ⌜keysEnsureCapacityDomain args⌝ ∗ True)%I.
Definition ReviewedKeysEnsureCapacityExit `{!islaG Sigma} `{!threadG}
    (args : EnsureCapacityArgs) (outcome : EnsureCapacityOutcome) :
    iProp Sigma :=
  (∃ (x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 : bv 64),
   reg_col (arrayListSysRegs (ensureInputEnd args)) ∗
   "x1" ↦ᵣ RVal_Bits (ensureReturnAddress args) ∗
   "x2" ↦ᵣ RVal_Bits (ensureStackPointer args) ∗
   "x5" ↦ᵣ RVal_Bits x5 ∗ "x6" ↦ᵣ RVal_Bits x6 ∗ "x7" ↦ᵣ RVal_Bits x7 ∗
   "x10" ↦ᵣ RVal_Bits x10 ∗ "x11" ↦ᵣ RVal_Bits x11 ∗ "x12" ↦ᵣ RVal_Bits x12 ∗
   "x13" ↦ᵣ RVal_Bits x13 ∗ "x14" ↦ᵣ RVal_Bits x14 ∗ "x15" ↦ᵣ RVal_Bits x15 ∗
   "x16" ↦ᵣ RVal_Bits x16 ∗ "x17" ↦ᵣ RVal_Bits x17 ∗
   "x28" ↦ᵣ RVal_Bits x28 ∗ "x29" ↦ᵣ RVal_Bits x29 ∗
   "x30" ↦ᵣ RVal_Bits x30 ∗ "x31" ↦ᵣ RVal_Bits x31 ∗
   arrayListSavedRegisters (ensureSaved args) ∗
   bv_unsigned (ensureListPointer args) ↦ₘ∗ arrayListHeaderBytes (ensureListAfter outcome) ∗
   arrayListBuffer keysElementBytes keysLog2Alignment (ensureListAfter outcome) ∗
   ziskExtraParamsAddress ↦ₘ∗ keysEnsureCapacityScratchAfter args outcome ∗
   altFlAllocatorObject (bv_unsigned (ensureAllocatorPointer args))
     (ensureAllocatorContext args) ∗
   altFlVtable ∗
   altFlHeap ∗
   (bv_unsigned (ensureStackPointer args) - keysEnsureCapacityStackBytes) ↦ₘ?
     keysEnsureCapacityStackBytes ∗
   ⌜bv_unsigned x10 = arrayListOutcomeCode (ensureKind outcome)⌝ ∗ True)%I.
Definition ReviewedKeysEnsureCapacityContractCode `{!islaG Sigma} `{!threadG} :
    iProp Sigma :=
  (keysEnsureCapacitySelectedCode ∗ altFlAllocatorPremises ∗
   ziskMemcpyCallPremise)%I.
Definition ReviewedKeysEnsureCapacityResources `{!islaG Sigma} `{!threadG}
    (returnAddress : Z) :
    IslarisContractResources EnsureCapacityArgs EnsureCapacityOutcome :=
  {| islarisCode := keysEnsureCapacityContractCode;
     islarisEntry := fun args =>
       (⌜bv_unsigned (ensureReturnAddress args) = returnAddress⌝ ∗
        keysEnsureCapacityEntry args)%I;
     islarisExit := keysEnsureCapacityExit |}.
Definition ReviewedKeysEnsureCapacityContractModel (returnAddress : Z) :
    IslarisContractModel EnsureCapacityArgs EnsureCapacityOutcome :=
  {| islarisContractAllows := fun args outcome =>
       bv_unsigned (ensureReturnAddress args) = returnAddress /\
       keysEnsureCapacityDomain args /\
       keysEnsureCapacityAllows args outcome;
     islarisContractStep :=
       ZesuSsz.Stock.Closure.index_ensureTotalCapacity.ensureTotalCapacity_cfg_step;
     islarisContractResources := fun Sigma HG HT =>
       @keysEnsureCapacityResources Sigma HG HT returnAddress |}.
Definition ReviewedKeysEnsureCapacityContractCorrect : Prop :=
  forall returnAddress,
    IslarisContractCorrect sym_array_list_Aligned_32_u8_null_ensureTotalCapacity
      returnAddress (keysEnsureCapacityContractModel returnAddress).
Check (eq_refl : @keysToOwnedSliceSelectedCode = @ReviewedKeysToOwnedSliceSelectedCode).
Check (eq_refl : @entriesToOwnedSliceSelectedCode = @ReviewedEntriesToOwnedSliceSelectedCode).
Check (eq_refl : @keysEnsureCapacitySelectedCode = @ReviewedKeysEnsureCapacitySelectedCode).
Check (eq_refl : @arrayListEmpty = @ReviewedArrayListEmpty).
Check (eq_refl : @arrayListHeaderBytes = @ReviewedArrayListHeaderBytes).
Check (eq_refl : @arrayListRamRange = @ReviewedArrayListRamRange).
Check (eq_refl : @arrayListWellFormed = @ReviewedArrayListWellFormed).
Check (eq_refl : @arrayListBuffer = @ReviewedArrayListBuffer).
Check (eq_refl : @arrayListOutcomeCode = @ReviewedArrayListOutcomeCode).
Check (eq_refl : @arrayListSavedRegisters = @ReviewedArrayListSavedRegisters).
Check (eq_refl : @arrayListSysRegs = @ReviewedArrayListSysRegs).
Check (eq_refl : @arrayListStackLayout = @ReviewedArrayListStackLayout).
Check (eq_refl : @arrayListResultImage = @ReviewedArrayListResultImage).
Check (eq_refl : @arrayListErrorImage = @ReviewedArrayListErrorImage).
Check (eq_refl : @toOwnedSliceDomain = @ReviewedToOwnedSliceDomain).
Check (eq_refl : @toOwnedSliceAllows = @ReviewedToOwnedSliceAllows).
Check (eq_refl : @toOwnedSliceScratchAfter = @ReviewedToOwnedSliceScratchAfter).
Check (eq_refl : @toOwnedSliceEntry = @ReviewedToOwnedSliceEntry).
Check (eq_refl : @toOwnedSliceExit = @ReviewedToOwnedSliceExit).
Check (eq_refl : @toOwnedSliceResources = @ReviewedToOwnedSliceResources).
Check (eq_refl : @toOwnedSliceModel = @ReviewedToOwnedSliceModel).
Check (eq_refl : @keysToOwnedSliceContractCode = @ReviewedKeysToOwnedSliceContractCode).
Check (eq_refl : @keysToOwnedSliceContractModel = @ReviewedKeysToOwnedSliceContractModel).
Check (eq_refl : @KeysToOwnedSliceContractCorrect = @ReviewedKeysToOwnedSliceContractCorrect).
Check (eq_refl : @entriesToOwnedSliceContractCode = @ReviewedEntriesToOwnedSliceContractCode).
Check (eq_refl : @entriesToOwnedSliceContractModel = @ReviewedEntriesToOwnedSliceContractModel).
Check (eq_refl : @EntriesToOwnedSliceContractCorrect = @ReviewedEntriesToOwnedSliceContractCorrect).
Check (eq_refl : @arrayListGrownCapacity = @ReviewedArrayListGrownCapacity).
Check (eq_refl : @keysEnsureCapacityDomain = @ReviewedKeysEnsureCapacityDomain).
Check (eq_refl : @keysEnsureCapacityAllows = @ReviewedKeysEnsureCapacityAllows).
Check (eq_refl : @keysEnsureCapacityScratchAfter = @ReviewedKeysEnsureCapacityScratchAfter).
Check (eq_refl : @keysEnsureCapacityEntry = @ReviewedKeysEnsureCapacityEntry).
Check (eq_refl : @keysEnsureCapacityExit = @ReviewedKeysEnsureCapacityExit).
Check (eq_refl : @keysEnsureCapacityContractCode = @ReviewedKeysEnsureCapacityContractCode).
Check (eq_refl : @keysEnsureCapacityResources = @ReviewedKeysEnsureCapacityResources).
Check (eq_refl : @keysEnsureCapacityContractModel = @ReviewedKeysEnsureCapacityContractModel).
Check (eq_refl : @KeysEnsureCapacityContractCorrect = @ReviewedKeysEnsureCapacityContractCorrect).
