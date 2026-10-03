Require Import ZesuSsz.Automation.CallSet.
Require Import ZesuSsz.Automation.ResourceGroups.
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Automation.UninitRegions.
Require Import ZesuSsz.Automation.SealedCoverage.
From iris.proofmode Require Import environments.

(* Select only a proved covering region. The existing subsumption rule
   checks the requested width and returns both remainder wands. *)
Ltac zesu_guarded_uninit_key :=
  zesu_call_set_on;
  zesu_step_sealed_open_on;
  zesu_expose_environment_alias;
  lazymatch goal with
  | |- envs_entails _ (find_in_context (FindMemMapsTo ?address) ?continuation) =>
    assert_fails (has_evar address);
    iMatchHyp ltac:(fun H owned =>
      lazymatch owned with (?base ↦ₘ? ?count)%I =>
        assert_fails (has_evar (base, count));
        let Hrange := fresh "HuninitSelection" in
        assert (Hrange : (base <= address < base + count \/ base = address)%Z)
          by zesu_region_bounds;
        clear Hrange
      end);
    let key := constr:(ZesuMemRegionSearch address) in
    simple notypeclasses refine (tac_find_in_context key _ _);
    [typeclasses eauto | simpl; repeat liExist false; liFindHypOrTrue key]
  end.
