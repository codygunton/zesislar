Require Import ZesuSsz.Automation.All.
Require Import ZesuSsz.Proofs.Tests.IntegerArrayAddress.

(* Remove release instances locally to preserve the switch-off checks. *)
Section ReleaseSwitchOff.
#[local] Remove Hints IntegerArrayAddress.zesu_switch_integer_array_address StoreMemoryLookup.zesu_store_integer_address : typeclass_instances.

Lemma integer_array_address_import_isolation : True.
Proof.
  Fail let _ := constr:(_ : ZesuStepIntegerArrayAddress) in idtac.
  exact I.
Qed.

End ReleaseSwitchOff.

Require Import ZesuSsz.Automation.All.
