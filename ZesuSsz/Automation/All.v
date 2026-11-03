Require Export InstrSpecs.Lookup.
Require Export InstrSpecs.Machine.
Require Export InstrSpecs.Specs.
Require Export ZesuSsz.Automation.Calls.
Require Export ZesuSsz.Automation.InstrPre.
Require Export ZesuSsz.Automation.Finish.
Require Export ZesuSsz.Automation.SignedMaskBranch.
Require Export ZesuSsz.Automation.ArrayContinuation.
Require Export ZesuSsz.Automation.WordIdentity.
Require Export ZesuSsz.Automation.CodecArrayRead.
Require Export ZesuSsz.Automation.Rewrites.
Require Export ZesuSsz.Automation.Hooks.
Require Export ZesuSsz.Automation.UninitRegions.
Require Export ZesuSsz.Automation.NatBitvectors.
Require Export ZesuSsz.Automation.ArrayPacking.
Require Export ZesuSsz.Automation.LoopIndex.
Require Export ZesuSsz.Automation.CanonicalFactAdapter.
Require Export ZesuSsz.Automation.UnionRuleComponents.
Require Export ZesuSsz.Evidence.EntryWitnessSelector.
Require Export ZesuSsz.Evidence.EntryWitnessInputs.
Require Export ZesuSsz.Automation.FractionalRead.
Require Export ZesuSsz.Automation.BranchUnsigned.
Require Export ZesuSsz.Automation.BranchCastUnsigned.
Require Export ZesuSsz.Automation.SymbolicByteCodec.

#[export] Instance zesu_union_branch_guards_enabled :
  ZesuSsz.Automation.BitvectorFacts.ZesuStepBranchGuards := I.
#[export] Instance zesu_union_symbolic_byte_codec_enabled :
  ZesuSsz.Automation.SymbolicByteCodec.ZesuStepSymbolicByteCodec := {}.

#[export] Instance zesu_explicit_v1 :
  ZesuSsz.Automation.PureFacts.ZesuRuleSetV1 := I.
Require Export ZesuSsz.Automation.MaskPresentation.
Require Export ZesuSsz.Automation.MaskWrapPresentation.
Require Export ZesuSsz.Automation.StoreMemoryLookup.

#[export] Instance zesu_union_mask_presentation_enabled :
  ZesuSsz.Automation.BitvectorFacts.ZesuStepMaskNormalizer := I.
#[export] Instance zesu_union_store_memory_lookup_enabled :
  ZesuSsz.Automation.StoreMemoryLookup.ZesuStepStoreMemoryLookup := {}.

Require Export ZesuSsz.Automation.AdditiveDecoder.
Require Export ZesuSsz.Automation.FramePacking.
Require Export ZesuSsz.Automation.FramePackingFinish.
#[export] Instance zesu_union_frame_packing_enabled :
  ZesuSsz.Automation.FramePacking.ZesuStepFramePacking := {}.

Require Export ZesuSsz.Automation.HypothesisCast.
Require Export ZesuSsz.Automation.ByteMaskCast.
Require Export ZesuSsz.Automation.ByteReconstruction.
Require Export ZesuSsz.Automation.RewriteBoundGuards.

#[export] Instance zesu_union_hypothesis_cast_enabled :
  ZesuSsz.Automation.HypothesisCast.ZesuStepHypothesisCast := {}.
#[export] Instance zesu_union_byte_mask_cast_enabled :
  ZesuSsz.Automation.ByteMaskCast.ZesuStepByteMaskCast := {}.
#[export] Instance zesu_union_byte_reconstruction_enabled :
  ZesuSsz.Automation.ByteReconstruction.ZesuStepByteReconstruction := {}.
#[export] Instance zesu_union_rewrite_bound_guards_enabled :
  ZesuSsz.Automation.RewriteBoundGuards.ZesuStepRewriteBoundGuards := I.

(* Record-field pruning requires the existing production filter selection. *)
Require Export ZesuSsz.Automation.Switches.FinisherOnce.


Require Export ZesuSsz.Automation.Switches.RegisterCollectionSelection.
Require Export ZesuSsz.Automation.Switches.PureFactHints.
Require Export ZesuSsz.Automation.MemoryAddress.
Require Export ZesuSsz.Automation.WrappedWord.
Require Export ZesuSsz.Automation.EntryWitnessFinish.
Require Export ZesuSsz.Automation.MemoryTupleConsumer.
Require Export ZesuSsz.Automation.SourceFactMatching.
Require Export ZesuSsz.Automation.SourceFactByteViews.
Require Export ZesuSsz.Automation.FrameImageRoundtrip.
Require Export ZesuSsz.Automation.LoopResourceBackedge.

#[export] Instance zesu_signed_mask_branch_enabled :
  ZesuSsz.Automation.SignedMaskBranch.ZesuStepSignedMaskBranch := {}.
#[export] Instance zesu_array_continuation_enabled :
  ZesuSsz.Automation.ArrayContinuation.ZesuStepArrayContinuation := {}.
#[export] Instance zesu_word_identity_enabled :
  ZesuSsz.Automation.WordIdentity.ZesuStepWordIdentity := {}.
#[export] Instance zesu_codec_array_read_enabled :
  ZesuSsz.Automation.CodecArrayRead.ZesuStepCodecArrayRead := {}.
#[export] Instance zesu_regcol_vm_compute_enabled :
  ZesuSsz.Automation.Hooks.ZesuStepRegcolVMCompute := {}.
#[export] Instance zesu_source_witnesses_enabled :
  ZesuSsz.Automation.SourceWitnessInputs.ZesuStepSourceWitnesses := I.

(* Reopen the canonical hook owner after all library imports. *)
Require Export ZesuSsz.Automation.Hooks.
