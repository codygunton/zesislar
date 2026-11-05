Require Import ZesuSsz.Automation.All.
Require Import ZesuSsz.Proofs.Tests.ArrayRegionCast.

(* Remove the release instances locally to preserve the isolation refusal. *)
Section ReleaseSwitchIsolation.
#[local] Remove Hints
  ZesuSsz.Automation.Switches.ArrayRegionBounds.zesu_switch_array_region_bounds
  ZesuSsz.Automation.StoreMemoryLookup.zesu_store_region_bounds
  ZesuSsz.Automation.CodecArrayRead.codec_read_regions : typeclass_instances.

Lemma array_region_cast_no_transitive_activation : True.
Proof.
  Fail zesu_switch_enabled constr:(ZesuSsz.Automation.ByteArrayLengths.ZesuStepArrayRegionBounds).
  Fail let _ := constr:(_ : ZesuStepArrayRegionBounds) in idtac.
  exact I.
Qed.

End ReleaseSwitchIsolation.
Require Import ZesuSsz.Automation.All.
