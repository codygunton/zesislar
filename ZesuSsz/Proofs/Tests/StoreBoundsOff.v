Require Import ZesuSsz.Automation.All.
Require Import isla.riscv64.riscv64.
Open Scope Z_scope.

(* Remove release instances locally to preserve the switch-off checks. *)
Section ReleaseSwitchOff.
#[local] Remove Hints StoreMemoryLookup.zesu_store_array_bounds Hooks.codec_read_bounds StoreMemoryLookup.zesu_store_region_bounds CodecArrayRead.codec_read_regions : typeclass_instances.

Lemma store_bounds_switch_off (out : Z) (storage : list byte)
    (Hlength : length storage = 40%nat) : True.
Proof.
  Fail assert (Henabled : ZesuStepArrayBounds) by typeclasses eauto.
  Fail assert (Hbound :
    (Z.to_nat (out + 8 - out) + N.to_nat 8 <= length storage)%nat)
    by zesu_array_bounds_if_enabled.
  exact I.
Qed.

Lemma store_lengths_switch_off (storage : list byte)
    (Hlength : length storage = 40%nat) : True.
Proof.
  Fail assert (Henabled : ZesuStepArrayRegionBounds) by typeclasses eauto.
  Fail assert (Hbound : (0 < length storage)%nat)
    by solve [zesu_byte_array_lengths_if_enabled; lia].
  exact I.
Qed.

End ReleaseSwitchOff.

Print Assumptions store_bounds_switch_off.
Print Assumptions store_lengths_switch_off.

Require Import ZesuSsz.Automation.All.
