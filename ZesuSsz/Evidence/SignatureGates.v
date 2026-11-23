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
   ParentHeaderExcessBlobGasAboveLimit; ParentHeaderTrailingItemMalformed;
   AccessListAddressLength; AccessListKeyLength;
   AccessListEntryTrailingBytes]).

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
  | AccessListAddressLength | AccessListKeyLength
  | AccessListEntryTrailingBytes => false
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

(* txAccessList (plan B1; statements reviewed 2026-11-23, PR #362). The
   reference decoder candidateAccessList and its call walk accessListCalls
   are pinned through the meaning and domain below; the runtime premises of
   alt_fl_alloc and the general ZisK memcpy are pinned body for body. *)
Require Import SailStdpp.Values.
Require Import ZesuSsz.Compliance.SailRunAccessList.
Require Import ZesuSsz.Contracts.Candidates.AccessListCandidate.
Require Import ZesuSsz.Contracts.TxAccessListBugTriggers.
Require Import ZesuSsz.Contracts.TxAccessListMeaning.
Require Import ZesuSsz.Contracts.AltFlAllocPremises.
Require Import ZesuSsz.Contracts.ZiskMemcpyPremise.
Require Import ZesuSsz.Contracts.KeysEnsureCapacitySelected.
Require Import ZesuSsz.Contracts.KeysToOwnedSliceSelected.
Require Import ZesuSsz.Contracts.EntriesToOwnedSliceSelected.
Require Import ZesuSsz.Contracts.TxAccessListSelected.
Require Import ZesuSsz.Contracts.TxAccessListContract.
Require ZesuSsz.Stock.Closure.index_txAccessList.
Require ZesuSsz.Stock.Closure.index_ensureTotalCapacity.
Require ZesuSsz.Stock.Closure.index_sliceBytes32.
Require ZesuSsz.Stock.Closure.index_sliceAccessList.
Require ZesuSsz.Stock.Closure.index_allocatorAlloc.
Require ZesuSsz.Stock.Closure.index_allocatorRemap.
Require ZesuSsz.Stock.Closure.index_allocatorFree.
Local Open Scope list_scope.
Local Open Scope Z_scope.

Check (@candidateAccessList : list byte -> AccessListCandidate).
Check (@accessListCalls : list byte -> list AccessListCall).

Definition ReviewedTxAccessListBugTrigger (bug : KnownBug) (input : list byte) : bool :=
  match bug with
  | AccessListAddressLength => accessListAddressLengthb input
  | AccessListKeyLength => accessListKeyLengthb input
  | AccessListEntryTrailingBytes => accessListEntryTrailingb input
  | RlpLongLengthWrap | ParentHeaderMissingRequiredField
  | ParentHeaderTrailingBytes | ParentHeaderSkippedFieldShape
  | ParentHeaderBlobGasUnaligned | RlpUintNonCanonical
  | ParentHeaderUintOver8 | ParentHeaderUndecodedFieldRejected
  | ParentHeaderExcessBlobGasAboveLimit
  | ParentHeaderTrailingItemMalformed => false
  end.

Check (eq_refl : txAccessListBugTrigger = ReviewedTxAccessListBugTrigger).

Definition ReviewedAccessListSailField (isList : bool) (headerLength payloadLength : Z)
    : AccessListSail.RlpFieldRef 0 (headerLength + payloadLength) payloadLength :=
  @AccessListSail.Build_RlpFieldRef 0 (headerLength + payloadLength) payloadLength
    (@AccessListSail.Build_StatelessInputSliceFields 0
       (headerLength + payloadLength) 0 (headerLength + payloadLength))
    isList payloadLength.

Definition ReviewedAccessListEncodedSpan (ref : AccessListSail.AccessListRef) : Z * Z :=
  let slice := projT2 (projT2 (AccessListSail.AccessListRef_encoded ref)) in
  (AccessListSail.StatelessInputSliceFields_bytes slice,
   AccessListSail.StatelessInputSliceFields_len slice).

Definition ReviewedTxAccessListSail (input : list byte)
    : option (SailOutcome AccessListSail.AccessListRef) :=
  match candidateDecodeItem input with
  | candidateSuccess isList headerLength payloadLength =>
      Some (runDecodeAccessList input
              (ReviewedAccessListSailField isList headerLength payloadLength))
  | candidateError => None
  end.

Definition ReviewedAccessListHeadersFit (input : list byte) : Prop :=
  List.Forall (fun call => headerFits (snd call)) (accessListCalls input).

Definition ReviewedTxAccessListDomain (input : list byte) : Prop :=
  ReviewedAccessListHeadersFit input /\
  match candidateDecodeItem input with
  | candidateSuccess _ headerLength payloadLength =>
      headerLength + payloadLength <= 2 ^ 30
  | candidateError => True
  end.

Definition ReviewedAccessListKeyCount (entries : list AccessListEntryValue) : Z :=
  fold_right (fun entry total => Z.of_nat (List.length (entryKeys entry)) + total)
    0 entries.

Definition ReviewedTxAccessListSailAgrees (input : list byte) : Prop :=
  match candidateDecodeItem input with
  | candidateError => True
  | candidateSuccess _ headerLength payloadLength =>
      match candidateAccessList input with
      | accessListAccepted entries _ =>
          exists ref,
            ReviewedTxAccessListSail input = Some (Success ref) /\
            accessListCounts (Success ref) =
              Some (Z.of_nat (List.length entries),
                    ReviewedAccessListKeyCount entries) /\
            ReviewedAccessListEncodedSpan ref = (headerLength, payloadLength)
      | accessListRejected _ =>
          ReviewedTxAccessListSail input = Some (Reject RlpDecode)
      end
  end.

Definition ReviewedAccessListCandidateConsumed (candidate : AccessListCandidate) : Z :=
  match candidate with
  | accessListAccepted _ consumed => consumed
  | accessListRejected (Some consumed) => consumed
  | accessListRejected None => 0
  end.

Definition ReviewedTxAccessListOutcomeAllowed (input : list byte)
    (outcome : TxAccessListOutcomeClass) (consumed : Z) : Prop :=
  match outcome with
  | txAccessListOk entries =>
      candidateAccessList input = accessListAccepted entries consumed
  | txAccessListInvalidInput =>
      (exists rejected, candidateAccessList input = accessListRejected rejected) /\
      consumed = ReviewedAccessListCandidateConsumed (candidateAccessList input)
  | txAccessListAllocationFailure =>
      exists headerLength payloadLength,
        candidateDecodeItem input =
          candidateSuccess true headerLength payloadLength /\
        0 < payloadLength /\
        consumed = (headerLength + payloadLength) mod 2 ^ 64
  end.

Definition ReviewedTxAccessListMeaningModuloKnownBugs (input : list byte)
    (outcome : TxAccessListOutcomeClass) (consumed : Z) : Prop :=
  ReviewedTxAccessListDomain input /\
  ReviewedTxAccessListOutcomeAllowed input outcome consumed /\
  (ReviewedTxAccessListSailAgrees input \/
   exists bug, List.In bug knownBugs /\
     ReviewedTxAccessListBugTrigger bug input = true).

Check (eq_refl : accessListSailField = ReviewedAccessListSailField).
Check (eq_refl : accessListEncodedSpan = ReviewedAccessListEncodedSpan).
Check (eq_refl : txAccessListSail = ReviewedTxAccessListSail).
Check (eq_refl : accessListHeadersFit = ReviewedAccessListHeadersFit).
Check (eq_refl : txAccessListDomain = ReviewedTxAccessListDomain).
Check (eq_refl : accessListKeyCount = ReviewedAccessListKeyCount).
Check (eq_refl : txAccessListSailAgrees = ReviewedTxAccessListSailAgrees).
Check (eq_refl : accessListCandidateConsumed = ReviewedAccessListCandidateConsumed).
Check (eq_refl : txAccessListOutcomeAllowed = ReviewedTxAccessListOutcomeAllowed).
Check (eq_refl : TxAccessListMeaningModuloKnownBugs =
                 ReviewedTxAccessListMeaningModuloKnownBugs).

(* The runtime premises of alt_fl_alloc (alloc 0x80042494, remap
   0x8004218c, free 0x80041f38) and of memcpy (0x800e06c0) in general. *)
Definition ReviewedAltFlAllocatedBytes (pointer bytes : Z) : Z :=
  if pointer =? 0 then 0 else bytes.

Definition ReviewedAltFlVtableBytes : list byte :=
  word64Bytes 0x80042494 ++ word64Bytes 0x800421b0 ++
  word64Bytes 0x8004218c ++ word64Bytes 0x80041f38.

Definition ReviewedAltFlAllocatorBytes (context : Z) : list byte :=
  word64Bytes context ++ word64Bytes 0x801136d8.

Definition ReviewedAltFlAllocDomain (bytes log2Align : Z) : Prop :=
  0 < bytes < 2 ^ 63 /\ 0 <= log2Align <= 3.

Definition ReviewedAltFlAllocCallSpec `{!islaG Sigma} `{!threadG} : iProp Sigma :=
  (machine_call decodeItemCallMap 16
    (fun argv sp RET =>
      ⌜ReviewedAltFlAllocDomain (bv_unsigned (argv !!! 1%nat))
        (bv_unsigned (argv !!! 2%nat))⌝ ∗
      altFlHeap ∗
      RET (fun rets =>
        altFlHeap ∗
        bv_unsigned (rets !!! 0%nat) ↦ₘ?
          ReviewedAltFlAllocatedBytes (bv_unsigned (rets !!! 0%nat))
            (bv_unsigned (argv !!! 1%nat)) ∗
        altFlBlock (bv_unsigned (rets !!! 0%nat))
          (ReviewedAltFlAllocatedBytes (bv_unsigned (rets !!! 0%nat))
            (bv_unsigned (argv !!! 1%nat)))
          (bv_unsigned (argv !!! 2%nat)) ∗
        True)))%I.

Definition ReviewedAltFlRemapCallSpec `{!islaG Sigma} `{!threadG} : iProp Sigma :=
  (machine_call decodeItemCallMap 16
    (fun argv sp RET =>
      RET (fun rets => ⌜bv_unsigned (rets !!! 0%nat) = 0⌝ ∗ True)))%I.

Definition ReviewedAltFlFreeDomain (bytes log2Align : Z) : Prop :=
  0 < bytes < 2 ^ 63 /\ 0 <= log2Align <= 3.

Definition ReviewedAltFlFreeCallSpec `{!islaG Sigma} `{!threadG} : iProp Sigma :=
  (machine_call decodeItemCallMap 16
    (fun argv sp RET =>
      ⌜ReviewedAltFlFreeDomain (bv_unsigned (argv !!! 2%nat))
        (bv_unsigned (argv !!! 3%nat))⌝ ∗
      altFlHeap ∗
      bv_unsigned (argv !!! 1%nat) ↦ₘ? bv_unsigned (argv !!! 2%nat) ∗
      altFlBlock (bv_unsigned (argv !!! 1%nat)) (bv_unsigned (argv !!! 2%nat))
        (bv_unsigned (argv !!! 3%nat)) ∗
      RET (fun _ => altFlHeap ∗ True)))%I.

Definition ReviewedAltFlAllocCallPremise `{!islaG Sigma} `{!threadG} : iProp Sigma :=
  (□ instr_pre 0x80042494 ReviewedAltFlAllocCallSpec)%I.
Definition ReviewedAltFlRemapCallPremise `{!islaG Sigma} `{!threadG} : iProp Sigma :=
  (□ instr_pre 0x8004218c ReviewedAltFlRemapCallSpec)%I.
Definition ReviewedAltFlFreeCallPremise `{!islaG Sigma} `{!threadG} : iProp Sigma :=
  (□ instr_pre 0x80041f38 ReviewedAltFlFreeCallSpec)%I.

Check (eq_refl : altFlAllocatedBytes = ReviewedAltFlAllocatedBytes).
Check (eq_refl : altFlVtableBytes = ReviewedAltFlVtableBytes).
Check (eq_refl : altFlAllocatorBytes = ReviewedAltFlAllocatorBytes).
Check (eq_refl : altFlAllocDomain = ReviewedAltFlAllocDomain).
Check (eq_refl : @altFlAllocCallSpec = @ReviewedAltFlAllocCallSpec).
Check (eq_refl : @altFlRemapCallSpec = @ReviewedAltFlRemapCallSpec).
Check (eq_refl : altFlFreeDomain = ReviewedAltFlFreeDomain).
Check (eq_refl : @altFlFreeCallSpec = @ReviewedAltFlFreeCallSpec).
Check (eq_refl : @altFlAllocCallPremise = @ReviewedAltFlAllocCallPremise).
Check (eq_refl : @altFlRemapCallPremise = @ReviewedAltFlRemapCallPremise).
Check (eq_refl : @altFlFreeCallPremise = @ReviewedAltFlFreeCallPremise).

Definition ReviewedZiskMemcpyCallDomain (destination source length : Z) : Prop :=
  ziskWord destination /\ ziskWord source /\ ziskWord length /\
  ziskWritableSection stockZiskPermissions 0xa0400f00 8 /\
  (length <> 0 ->
    ziskMemcpyRange destination length /\
    ziskMemcpyRange source length /\
    ziskWritableSection stockZiskPermissions source length /\
    ziskWritableSection stockZiskPermissions destination length).

Definition ReviewedZiskMemcpyCallSpec `{!islaG Sigma} `{!threadG} : iProp Sigma :=
  (machine_call decodeItemCallMap 0
    (fun argv sp RET =>
      ∃ (source scratch : list byte),
      ⌜ReviewedZiskMemcpyCallDomain (bv_unsigned (argv !!! 0%nat))
        (bv_unsigned (argv !!! 1%nat)) (bv_unsigned (argv !!! 2%nat))⌝ ∗
      reg_col [(KindReg "zisk_input_end", BitsShape 64);
               (KindReg "zisk_free_input", BitsShape 64)] ∗
      bv_unsigned (argv !!! 1%nat) ↦ₘ∗ source ∗
      bv_unsigned (argv !!! 0%nat) ↦ₘ? bv_unsigned (argv !!! 2%nat) ∗
      0xa0400f00 ↦ₘ∗ scratch ∗
      ⌜Z.of_nat (length source) = bv_unsigned (argv !!! 2%nat)⌝ ∗
      ⌜length scratch = 8%nat⌝ ∗
      RET (fun _ =>
        reg_col [(KindReg "zisk_input_end", BitsShape 64);
                 (KindReg "zisk_free_input", BitsShape 64)] ∗
        bv_unsigned (argv !!! 1%nat) ↦ₘ∗ source ∗
        bv_unsigned (argv !!! 0%nat) ↦ₘ∗ source ∗
        0xa0400f00 ↦ₘ∗ word64Bytes (bv_unsigned (argv !!! 2%nat)) ∗
        True)))%I.

Definition ReviewedZiskMemcpyCallPremise `{!islaG Sigma} `{!threadG} : iProp Sigma :=
  (□ instr_pre 0x800e06c0 ReviewedZiskMemcpyCallSpec)%I.

Check (eq_refl : ziskMemcpyCallDomain = ReviewedZiskMemcpyCallDomain).
Check (eq_refl : @ziskMemcpyCallSpec = @ReviewedZiskMemcpyCallSpec).
Check (eq_refl : @ziskMemcpyCallPremise = @ReviewedZiskMemcpyCallPremise).

(* The Level 1 contract of txAccessList (entry 0x80000000). *)
Definition ReviewedTxRamRange (pointer length : Z) : Prop :=
  0xa0000000 <= pointer /\ 0 <= length /\ pointer + length <= 0xc0000000.

Definition ReviewedTxAccessListArgsRanges (args : TxAccessListArgs) : Prop :=
  0xa0000000 <= bv_unsigned (txResultPointer args) /\
  bv_unsigned (txResultPointer args) + 24 <= 0xc0000000 /\
  0xa0000000 <= bv_unsigned (txAllocatorPointer args) /\
  bv_unsigned (txAllocatorPointer args) + 16 <= 0xc0000000 /\
  0xa0000000 <= bv_unsigned (txRestPointer args) /\
  bv_unsigned (txRestPointer args) + 16 <= 0xc0000000 /\
  0xa0000000 + 576 + 128 <= bv_unsigned (txStackPointer args) /\
  bv_unsigned (txStackPointer args) <= 0xc0000000 /\
  bv_unsigned (txInputPointer args) + bv_unsigned (txInputLength args) <=
    bv_unsigned (txInputEnd args) /\
  ((2 ^ 30 <= bv_unsigned (txInputPointer args) /\
    bv_unsigned (txInputPointer args) + bv_unsigned (txInputLength args) <=
      2 ^ 31) \/
   (0xa0000000 <= bv_unsigned (txInputPointer args) /\
    bv_unsigned (txInputPointer args) + bv_unsigned (txInputLength args) <=
      0xc0000000)).

Definition ReviewedTxAccessListFrameBase (args : TxAccessListArgs) : Z :=
  bv_unsigned (txStackPointer args) - 576.

Definition ReviewedTxAccessListCalleeBase (args : TxAccessListArgs) : Z :=
  bv_unsigned (txStackPointer args) - 576 - 128.

Definition ReviewedTxAccessListArgsWellFormed (args : TxAccessListArgs) : Prop :=
  ReviewedTxAccessListArgsRanges args /\
  Z.of_nat (List.length (txInputBytes args)) =
    bv_unsigned (txInputLength args) /\
  bv_unsigned (txStackPointer args) mod 16 = 0 /\
  bv_unsigned (txReturnAddress args) mod 4 = 0 /\
  Z.of_nat (List.length (txScratchBefore args)) = 8 /\
  separateRanges (bv_unsigned (txResultPointer args)) 24
    (bv_unsigned (txAllocatorPointer args)) 16 /\
  separateRanges (bv_unsigned (txResultPointer args)) 24
    (bv_unsigned (txRestPointer args)) 16 /\
  separateRanges (bv_unsigned (txAllocatorPointer args)) 16
    (bv_unsigned (txRestPointer args)) 16 /\
  separateRanges (bv_unsigned (txInputPointer args))
    (bv_unsigned (txInputLength args))
    (bv_unsigned (txResultPointer args)) 24 /\
  separateRanges (bv_unsigned (txInputPointer args))
    (bv_unsigned (txInputLength args))
    (bv_unsigned (txAllocatorPointer args)) 16 /\
  separateRanges (bv_unsigned (txInputPointer args))
    (bv_unsigned (txInputLength args))
    (bv_unsigned (txRestPointer args)) 16 /\
  separateRanges (ReviewedTxAccessListCalleeBase args) (576 + 128)
    (bv_unsigned (txResultPointer args)) 24 /\
  separateRanges (ReviewedTxAccessListCalleeBase args) (576 + 128)
    (bv_unsigned (txAllocatorPointer args)) 16 /\
  separateRanges (ReviewedTxAccessListCalleeBase args) (576 + 128)
    (bv_unsigned (txRestPointer args)) 16 /\
  separateRanges (ReviewedTxAccessListCalleeBase args) (576 + 128)
    (bv_unsigned (txInputPointer args)) (bv_unsigned (txInputLength args)) /\
  ReviewedTxAccessListDomain (txInputBytes args).

Definition ReviewedTxAccessListEntryBytes (entry : AccessListEntryValue)
    (image : TxAccessListEntryImage) : list byte :=
  word64Bytes (imageKeysPointer image) ++
  word64Bytes (Z.of_nat (List.length (entryKeys entry))) ++
  entryAddress entry ++ imagePadding image.

Definition ReviewedTxAccessListEntriesBytes (entries : list AccessListEntryValue)
    (images : list TxAccessListEntryImage) : list byte :=
  concat (zip_with ReviewedTxAccessListEntryBytes entries images).

Definition ReviewedTxAccessListResultImage (outcome : TxAccessListOutcome) : Prop :=
  (List.length (txResultBytes outcome) = 24)%nat /\
  match txOutcomeClass outcome with
  | txAccessListOk entries =>
      word64At (txResultBytes outcome) 0 (txEntriesPointer outcome) /\
      word64At (txResultBytes outcome) 8 (Z.of_nat (List.length entries)) /\
      byteAt (txResultBytes outcome) 16 0 /\ byteAt (txResultBytes outcome) 17 0
  | txAccessListInvalidInput | txAccessListAllocationFailure =>
      txResultBytes outcome = word64Bytes 0 ++ word64Bytes 0 ++ word64Bytes 3
  end.

Definition ReviewedTxAccessListHeapImage (outcome : TxAccessListOutcome) : Prop :=
  match txOutcomeClass outcome with
  | txAccessListOk entries =>
      List.length (txEntryImages outcome) = List.length entries /\
      txLeakedBlocks outcome = [] /\
      (entries <> [] ->
       ReviewedTxRamRange (txEntriesPointer outcome)
         (40 * Z.of_nat (List.length entries))) /\
      Forall2 (fun entry image =>
        Z.of_nat (List.length (imagePadding image)) = 4 /\
        (entryKeys entry <> [] ->
         ReviewedTxRamRange (imageKeysPointer image)
           (32 * Z.of_nat (List.length (entryKeys entry)))))
        entries (txEntryImages outcome)
  | txAccessListInvalidInput | txAccessListAllocationFailure =>
      txEntryImages outcome = [] /\
      Forall (fun block =>
        0 < leakedBytes block /\
        ReviewedTxRamRange (leakedPointer block) (leakedBytes block) /\
        (leakedLog2Align block = 0 \/ leakedLog2Align block = 3))
        (txLeakedBlocks outcome)
  end.

Definition ReviewedTxAccessListAllows (args : TxAccessListArgs)
    (outcome : TxAccessListOutcome) : Prop :=
  ReviewedTxAccessListMeaningModuloKnownBugs (txInputBytes args)
    (txOutcomeClass outcome) (txConsumed outcome) /\
  ReviewedTxAccessListResultImage outcome /\
  ReviewedTxAccessListHeapImage outcome /\
  List.length (txAfterFrame outcome) = Z.to_nat 576 /\
  Z.of_nat (List.length (txScratchAfter outcome)) = 8.

Definition ReviewedTxAccessListSysRegs (args : TxAccessListArgs) :
    list (reg_kind * valu_shape) :=
  map (fun '(r, shape) =>
    (r, if decide (r = KindReg "zisk_input_end")
        then ExactShape (RVal_Bits (txInputEnd args))
        else shape)) zesu_sys_regs.

Definition ReviewedTxAccessListSelectedCode `{!islaG Sigma} `{!threadG} :
    iProp Sigma :=
  instr_lookup_resources
    (selectedCodeLookup ZesuSsz.Stock.Closure.index_txAccessList.instr_map).

Definition ReviewedTxAccessListContractCode `{!islaG Sigma} `{!threadG}
    : iProp Sigma :=
  (ReviewedTxAccessListSelectedCode ∗ keysEnsureCapacitySelectedCode ∗
   keysToOwnedSliceSelectedCode ∗ entriesToOwnedSliceSelectedCode ∗
   decodeItemSelectedCode ∗ ReviewedZiskMemcpyCallPremise ∗
   ReviewedAltFlAllocCallPremise ∗ ReviewedAltFlRemapCallPremise ∗
   ReviewedAltFlFreeCallPremise)%I.

Definition ReviewedTxOwnedSlice `{!islaG Sigma} `{!threadG}
    (pointer log2Align : Z) (bytes : list byte) : iProp Sigma :=
  (match bytes with
   | [] => True
   | _ :: _ => pointer ↦ₘ∗ bytes ∗
               altFlBlock pointer (Z.of_nat (List.length bytes)) log2Align
   end)%I.

Definition ReviewedTxAccessListReturnedHeap `{!islaG Sigma} `{!threadG}
    (outcome : TxAccessListOutcome) : iProp Sigma :=
  (match txOutcomeClass outcome with
   | txAccessListOk entries =>
       ReviewedTxOwnedSlice (txEntriesPointer outcome) 3
         (ReviewedTxAccessListEntriesBytes entries (txEntryImages outcome)) ∗
       [∗ list] entry; image ∈ entries; txEntryImages outcome,
         ReviewedTxOwnedSlice (imageKeysPointer image) 0
           (concat (entryKeys entry))
   | txAccessListInvalidInput | txAccessListAllocationFailure => True
   end ∗
   [∗ list] block ∈ txLeakedBlocks outcome,
     leakedPointer block ↦ₘ? leakedBytes block ∗
     altFlBlock (leakedPointer block) (leakedBytes block)
       (leakedLog2Align block))%I.

Definition ReviewedTxAccessListEntryResources `{!islaG Sigma} `{!threadG}
    (args : TxAccessListArgs) : iProp Sigma :=
  (∃ (x5 x6 x7 x13 x14 x15 x16 x17 x28 x29 x30 x31 : bv 64),
   reg_col (ReviewedTxAccessListSysRegs args) ∗
   "x1" ↦ᵣ RVal_Bits (txReturnAddress args) ∗
   "x2" ↦ᵣ RVal_Bits (txStackPointer args) ∗
   "x5" ↦ᵣ RVal_Bits x5 ∗ "x6" ↦ᵣ RVal_Bits x6 ∗ "x7" ↦ᵣ RVal_Bits x7 ∗
   "x8" ↦ᵣ RVal_Bits (txSavedX8 args) ∗
   "x9" ↦ᵣ RVal_Bits (txSavedX9 args) ∗
   "x10" ↦ᵣ RVal_Bits (txResultPointer args) ∗
   "x11" ↦ᵣ RVal_Bits (txAllocatorPointer args) ∗
   "x12" ↦ᵣ RVal_Bits (txRestPointer args) ∗
   "x13" ↦ᵣ RVal_Bits x13 ∗ "x14" ↦ᵣ RVal_Bits x14 ∗ "x15" ↦ᵣ RVal_Bits x15 ∗
   "x16" ↦ᵣ RVal_Bits x16 ∗ "x17" ↦ᵣ RVal_Bits x17 ∗
   "x18" ↦ᵣ RVal_Bits (txSavedX18 args) ∗
   "x19" ↦ᵣ RVal_Bits (txSavedX19 args) ∗
   "x20" ↦ᵣ RVal_Bits (txSavedX20 args) ∗
   "x21" ↦ᵣ RVal_Bits (txSavedX21 args) ∗
   "x22" ↦ᵣ RVal_Bits (txSavedX22 args) ∗
   "x23" ↦ᵣ RVal_Bits (txSavedX23 args) ∗
   "x24" ↦ᵣ RVal_Bits (txSavedX24 args) ∗
   "x25" ↦ᵣ RVal_Bits (txSavedX25 args) ∗
   "x26" ↦ᵣ RVal_Bits (txSavedX26 args) ∗
   "x27" ↦ᵣ RVal_Bits (txSavedX27 args) ∗
   "x28" ↦ᵣ RVal_Bits x28 ∗ "x29" ↦ᵣ RVal_Bits x29 ∗
   "x30" ↦ᵣ RVal_Bits x30 ∗ "x31" ↦ᵣ RVal_Bits x31 ∗
   bv_unsigned (txInputPointer args) ↦ₘ∗ txInputBytes args ∗
   bv_unsigned (txRestPointer args) ↦ₘ∗
     (word64Bytes (bv_unsigned (txInputPointer args)) ++
      word64Bytes (bv_unsigned (txInputLength args))) ∗
   bv_unsigned (txAllocatorPointer args) ↦ₘ∗
     ReviewedAltFlAllocatorBytes (bv_unsigned (txAllocatorContext args)) ∗
   0x801136d8 ↦ₘ∗ ReviewedAltFlVtableBytes ∗
   altFlHeap ∗
   0xa0400f00 ↦ₘ∗ txScratchBefore args ∗
   bv_unsigned (txResultPointer args) ↦ₘ? 24 ∗
   ReviewedTxAccessListFrameBase args ↦ₘ? 576 ∗
   ReviewedTxAccessListCalleeBase args ↦ₘ? 128 ∗
   ⌜ReviewedTxAccessListArgsWellFormed args⌝ ∗ True)%I.

Definition ReviewedTxAccessListExitResources `{!islaG Sigma} `{!threadG}
    (args : TxAccessListArgs) (outcome : TxAccessListOutcome) : iProp Sigma :=
  (∃ (x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 : bv 64),
   reg_col zesu_sys_regs ∗
   "x1" ↦ᵣ RVal_Bits (txReturnAddress args) ∗
   "x2" ↦ᵣ RVal_Bits (txStackPointer args) ∗
   "x5" ↦ᵣ RVal_Bits x5 ∗ "x6" ↦ᵣ RVal_Bits x6 ∗ "x7" ↦ᵣ RVal_Bits x7 ∗
   "x8" ↦ᵣ RVal_Bits (txSavedX8 args) ∗
   "x9" ↦ᵣ RVal_Bits (txSavedX9 args) ∗
   "x10" ↦ᵣ RVal_Bits x10 ∗ "x11" ↦ᵣ RVal_Bits x11 ∗ "x12" ↦ᵣ RVal_Bits x12 ∗
   "x13" ↦ᵣ RVal_Bits x13 ∗ "x14" ↦ᵣ RVal_Bits x14 ∗ "x15" ↦ᵣ RVal_Bits x15 ∗
   "x16" ↦ᵣ RVal_Bits x16 ∗ "x17" ↦ᵣ RVal_Bits x17 ∗
   "x18" ↦ᵣ RVal_Bits (txSavedX18 args) ∗
   "x19" ↦ᵣ RVal_Bits (txSavedX19 args) ∗
   "x20" ↦ᵣ RVal_Bits (txSavedX20 args) ∗
   "x21" ↦ᵣ RVal_Bits (txSavedX21 args) ∗
   "x22" ↦ᵣ RVal_Bits (txSavedX22 args) ∗
   "x23" ↦ᵣ RVal_Bits (txSavedX23 args) ∗
   "x24" ↦ᵣ RVal_Bits (txSavedX24 args) ∗
   "x25" ↦ᵣ RVal_Bits (txSavedX25 args) ∗
   "x26" ↦ᵣ RVal_Bits (txSavedX26 args) ∗
   "x27" ↦ᵣ RVal_Bits (txSavedX27 args) ∗
   "x28" ↦ᵣ RVal_Bits x28 ∗ "x29" ↦ᵣ RVal_Bits x29 ∗
   "x30" ↦ᵣ RVal_Bits x30 ∗ "x31" ↦ᵣ RVal_Bits x31 ∗
   bv_unsigned (txInputPointer args) ↦ₘ∗ txInputBytes args ∗
   bv_unsigned (txRestPointer args) ↦ₘ∗
     (word64Bytes (bv_unsigned (txInputPointer args) + txConsumed outcome) ++
      word64Bytes (bv_unsigned (txInputLength args) - txConsumed outcome)) ∗
   bv_unsigned (txAllocatorPointer args) ↦ₘ∗
     ReviewedAltFlAllocatorBytes (bv_unsigned (txAllocatorContext args)) ∗
   0x801136d8 ↦ₘ∗ ReviewedAltFlVtableBytes ∗
   altFlHeap ∗
   0xa0400f00 ↦ₘ∗ txScratchAfter outcome ∗
   bv_unsigned (txResultPointer args) ↦ₘ∗ txResultBytes outcome ∗
   ReviewedTxAccessListFrameBase args ↦ₘ∗ txAfterFrame outcome ∗
   ReviewedTxAccessListCalleeBase args ↦ₘ? 128 ∗
   ReviewedTxAccessListReturnedHeap outcome ∗ True)%I.

Definition ReviewedTxAccessListContractResources `{!islaG Sigma} `{!threadG}
    (returnAddress : Z) :
    IslarisContractResources TxAccessListArgs TxAccessListOutcome :=
  {| islarisCode := ReviewedTxAccessListContractCode;
     islarisEntry := fun args =>
       (⌜bv_unsigned (txReturnAddress args) = returnAddress⌝ ∗
        ReviewedTxAccessListEntryResources args)%I;
     islarisExit := ReviewedTxAccessListExitResources |}.

Definition ReviewedTxAccessListContractModel (returnAddress : Z) :
    IslarisContractModel TxAccessListArgs TxAccessListOutcome :=
  {| islarisContractAllows := fun args outcome =>
       bv_unsigned (txReturnAddress args) = returnAddress /\
       ReviewedTxAccessListAllows args outcome;
     islarisContractStep := fun source target =>
       ZesuSsz.Stock.Closure.index_txAccessList.txAccessList_cfg_step
         source target \/
       ZesuSsz.Stock.Closure.index_decodeItem.decodeItem_cfg_step
         source target \/
       ZesuSsz.Stock.Closure.index_ensureTotalCapacity.ensureTotalCapacity_cfg_step
         source target \/
       ZesuSsz.Stock.Closure.index_sliceBytes32.sliceBytes32_cfg_step
         source target \/
       ZesuSsz.Stock.Closure.index_sliceAccessList.sliceAccessList_cfg_step
         source target \/
       ZesuSsz.Stock.Closure.index_allocatorAlloc.allocatorAlloc_cfg_step
         source target \/
       ZesuSsz.Stock.Closure.index_allocatorRemap.allocatorRemap_cfg_step
         source target \/
       ZesuSsz.Stock.Closure.index_allocatorFree.allocatorFree_cfg_step
         source target \/
       ZesuSsz.Stock.Closure.index_memcpyStub.memcpyStub_cfg_step
         source target;
     islarisContractResources := fun Sigma HG HT =>
       @ReviewedTxAccessListContractResources Sigma HG HT returnAddress |}.

Definition ReviewedTxAccessListContractCorrect : Prop :=
  forall returnAddress,
    IslarisContractCorrect 0x80000000 returnAddress
      (ReviewedTxAccessListContractModel returnAddress).

Check (eq_refl : @txAccessListSelectedCode = @ReviewedTxAccessListSelectedCode).
Check (eq_refl : txRamRange = ReviewedTxRamRange).
Check (eq_refl : txAccessListArgsRanges = ReviewedTxAccessListArgsRanges).
Check (eq_refl : txAccessListArgsWellFormed = ReviewedTxAccessListArgsWellFormed).
Check (eq_refl : txAccessListEntriesBytes = ReviewedTxAccessListEntriesBytes).
Check (eq_refl : txAccessListAllows = ReviewedTxAccessListAllows).
Check (eq_refl : @txAccessListContractCode = @ReviewedTxAccessListContractCode).
Check (eq_refl : @txAccessListEntryResources = @ReviewedTxAccessListEntryResources).
Check (eq_refl : @txAccessListExitResources = @ReviewedTxAccessListExitResources).
Check (eq_refl : TxAccessListContractCorrect = ReviewedTxAccessListContractCorrect).
