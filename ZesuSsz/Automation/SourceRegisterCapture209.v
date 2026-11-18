Require Import ZesuSsz.Automation.SourceRegisterCodec203.
Require Import ZesuSsz.Automation.SourceRegisterOrigin194.
Require Import ZesuSsz.Automation.SourceWitnessInputs.
Require Import ZesuSsz.Evidence.EntryWitnessInputs.
Require Import isla.riscv64.riscv64.
Require Import isla.automation.
From iris.proofmode Require Import environments.

Ltac zesu_capture_source_register_post203 :=
  try lazymatch goal with
  | |- envs_entails _
      (@zesu_source_register_post _ _ _ _ ?width _ ?value) =>
      is_closed_term width;
      lazymatch value with
      | Val_Bits (@bv_to_bvn ?actual_width _) =>
          constr_eq actual_width width;
          rewrite zesu_source_register_post_bits203
      end
  end;
  lazymatch goal with
  | |- envs_entails _
      (@bi_wand _ (@bi_pure _
        (@ZesuSourceWitness (bv ?width) ?key ?word)) _) =>
      is_closed_term width;
      EntryWitnessInputs.zesu_witness_resolved key;
      EntryWitnessInputs.zesu_witness_resolved word;
      li_unfold_lets_in_context;
      let name := iFresh in iIntros name;
      let marker := fresh "HsourceRegisterWitness" in
      pose (marker := @ZesuSourceWitnessHere (bv width) key word)
  end.
