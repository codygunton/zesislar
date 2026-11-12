Require Export InstrSpecs.Lookup.
Require Export InstrSpecs.Machine.
Require Export InstrSpecs.Specs.
Require Export ZesuSsz.Automation2.Calls.
Require Export ZesuSsz.Automation2.InstrPre.
Require Export ZesuSsz.Automation2.Finish.
Require Export ZesuSsz.Automation2.SignedMaskBranch.
Require Export ZesuSsz.Automation2.ArrayContinuation.
Require Export ZesuSsz.Automation2.WordIdentity.
Require Export ZesuSsz.Automation2.CodecArrayRead.
Require Export ZesuSsz.Automation2.Rewrites.
Require Export ZesuSsz.Automation2.Hooks.
Require Export ZesuSsz.Automation2.ResidualLemmas.
Require Export ZesuSsz.Automation2.UninitRegions.
Require Export ZesuSsz.Automation2.FrozenDuplicates.
Require Export ZesuSsz.Automation2.NatBitvectors.
Require Export ZesuSsz.Automation2.ArrayPacking.
Require Export ZesuSsz.Automation2.LoopIndex.
Require Export ZesuSsz.Automation2.CanonicalFactAdapter.
Require Export ZesuSsz.Automation2.UnionRuleComponents.
Require Export ZesuSsz.Evidence.EntryWitnessSelector.
Require Export ZesuSsz.Evidence.EntryWitnessInputs.
Require Export ZesuSsz.Automation2.FractionalRead.
Require Export ZesuSsz.Automation2.BranchUnsigned.
Require Export ZesuSsz.Automation2.BranchCastUnsigned.
Require Export ZesuSsz.Automation2.SymbolicByteCodec.

#[export] Instance zesu_union_branch_guards_enabled :
  ZesuSsz.Automation2.BitvectorFacts.ZesuStepBranchGuards := I.
#[export] Instance zesu_union_symbolic_byte_codec_enabled :
  ZesuSsz.Automation2.SymbolicByteCodec.ZesuStepSymbolicByteCodec := {}.

#[export] Instance zesu_explicit_v1 :
  ZesuSsz.Automation2.PureFacts.ZesuRuleSetV1 := I.
Require Export ZesuSsz.Automation2.MaskPresentation.
Require Export ZesuSsz.Automation2.MaskWrapPresentation.
Require Export ZesuSsz.Automation2.StoreMemoryLookup.

#[export] Instance zesu_union_mask_presentation_enabled :
  ZesuSsz.Automation2.BitvectorFacts.ZesuStepMaskNormalizer := I.
#[export] Instance zesu_union_store_memory_lookup_enabled :
  ZesuSsz.Automation2.StoreMemoryLookup.ZesuStepStoreMemoryLookup := {}.

Require Export ZesuSsz.Automation2.AdditiveDecoder.
Require Export ZesuSsz.Automation2.FramePacking.
Require Export ZesuSsz.Automation2.FramePackingFinish.
#[export] Instance zesu_union_frame_packing_enabled :
  ZesuSsz.Automation2.FramePacking.ZesuStepFramePacking := {}.

Require Export ZesuSsz.Automation2.HypothesisCast.
Require Export ZesuSsz.Automation2.ByteMaskCast.
Require Export ZesuSsz.Automation2.ByteReconstruction.
Require Export ZesuSsz.Automation2.RewriteBoundGuards.

#[export] Instance zesu_union_hypothesis_cast_enabled :
  ZesuSsz.Automation2.HypothesisCast.ZesuStepHypothesisCast := {}.
#[export] Instance zesu_union_byte_mask_cast_enabled :
  ZesuSsz.Automation2.ByteMaskCast.ZesuStepByteMaskCast := {}.
#[export] Instance zesu_union_byte_reconstruction_enabled :
  ZesuSsz.Automation2.ByteReconstruction.ZesuStepByteReconstruction := {}.
#[export] Instance zesu_union_rewrite_bound_guards_enabled :
  ZesuSsz.Automation2.RewriteBoundGuards.ZesuStepRewriteBoundGuards := I.

(* Record-field pruning requires the existing production filter selection. *)
Require Export ZesuSsz.Automation2.Switches.FinisherOnce.


Require Export ZesuSsz.Automation2.Switches.RegisterCollectionSelection.
Require Export ZesuSsz.Automation2.Switches.PureFactHints.
Require Export ZesuSsz.Automation2.MemoryAddress.
Require Export ZesuSsz.Automation2.WrappedWord.
Require Export ZesuSsz.Automation2.EntryWitnessFinish.
Require Export ZesuSsz.Automation2.MemoryTupleConsumer.
Require Export ZesuSsz.Automation2.SourceFactMatching.
Require Export ZesuSsz.Automation2.SourceFactByteViews.
Require Export ZesuSsz.Automation2.FrameImageRoundtrip.
Require Export ZesuSsz.Automation2.LoopResourceBackedge.
Require Export ZesuSsz.Automation2.CodecRoundtrip.
Require Export ZesuSsz.Automation2.CodecFrame.

#[export] Instance zesu_signed_mask_branch_enabled :
  ZesuSsz.Automation2.SignedMaskBranch.ZesuStepSignedMaskBranch := {}.
#[export] Instance zesu_array_continuation_enabled :
  ZesuSsz.Automation2.ArrayContinuation.ZesuStepArrayContinuation := {}.
#[export] Instance zesu_word_identity_enabled :
  ZesuSsz.Automation2.WordIdentity.ZesuStepWordIdentity := {}.
#[export] Instance zesu_codec_array_read_enabled :
  ZesuSsz.Automation2.CodecArrayRead.ZesuStepCodecArrayRead := {}.
#[export] Instance zesu_regcol_vm_compute_enabled :
  ZesuSsz.Automation2.Hooks.ZesuStepRegcolVMCompute := {}.
#[export] Instance zesu_source_witnesses_enabled :
  ZesuSsz.Automation2.SourceWitnessInputs.ZesuStepSourceWitnesses := I.
#[export] Instance zesu_codec_frame_enabled :
  ZesuSsz.Automation2.CodecFrame.ZesuStepCodecFrame := {}.

(* Reopen the canonical hook owner after all library imports. *)
Require Export ZesuSsz.Automation2.Hooks.
