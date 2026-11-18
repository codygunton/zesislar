Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Automation.SwitchDispatch.
Require Import ZesuSsz.Automation.Hooks.
Require Import ZesuSsz.Automation.ByteArrayLengths.
Require Import ZesuSsz.Automation.ResourceGroups.
From stdpp Require Import bitvector.definitions list.
From Coq Require Import Lists.List ZArith.ZArith.
From iris.proofmode Require Import environments.
Local Open Scope Z_scope.

Class ZesuStepCodecArrayLookup : Prop := {}.

#[export] Instance codec_array_integer_address `{ZesuStepCodecArrayLookup} :
  ZesuSsz.Automation.Hooks.ZesuStepIntegerArrayAddress := I.
#[export] Instance codec_array_bounds `{ZesuStepCodecArrayLookup} :
  ZesuSsz.Automation.Hooks.ZesuStepArrayBounds := I.
#[export] Instance codec_array_region_bounds `{ZesuStepCodecArrayLookup} :
  ZesuSsz.Automation.ByteArrayLengths.ZesuStepArrayRegionBounds := I.

(* Keep the canonical length equation during collection. The public theorem
   proves it from a nonnegative count; no bytes or ownership are converted. *)
Ltac zesu_owned_codec_length_facts values :=
  repeat multimatch values with
  | context [bv_to_little_endian ?count ?width ?value] =>
      assert_fails (match goal with
      | _ : length (bv_to_little_endian count width value) = Z.to_nat count |- _ => idtac
      end);
      let nonnegative := fresh "HcodecCountNonnegative" in
      assert (nonnegative : (0 <= count)%Z) by first [assumption | lia];
      let equation := fresh "HownedCodecLength" in
      pose proof (length_bv_to_little_endian count width value nonnegative) as equation;
      clear nonnegative
  end.

Ltac zesu_collect_owned_codec_lengths spatial :=
  lazymatch spatial with
  | environments.Enil => idtac
  | environments.Esnoc ?rest ?name ?resource =>
      zesu_collect_owned_codec_lengths rest;
      lazymatch resource with
      | @mem_mapsto_array _ _ 8%N _ _ ?values =>
          zesu_owned_codec_length_facts values
      | _ => idtac
      end
  end.

(* This changes only the finder dispatch. The existing region rule chooses
   the same array, and the existing read consumer retains its complete owner. *)
Ltac zesu_codec_array_lookup :=
  ZesuSsz.Automation.SwitchDispatch.zesu_switch_enabled
    constr:(ZesuStepCodecArrayLookup);
  ZesuSsz.Automation.ResourceGroups.zesu_expose_environment_alias;
  lazymatch goal with
  | |- environments.envs_entails ?context
      (find_in_context (FindMemMapsTo _) _) =>
      let spatial := eval cbn [environments.env_spatial] in
        (environments.env_spatial context) in
      zesu_collect_owned_codec_lengths spatial;
      progress ZesuSsz.Automation.Hooks.zesu_integer_array_address_if_enabled;
      liEnsureInvariant;
      liStep
  end.
