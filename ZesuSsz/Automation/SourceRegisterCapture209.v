Require Import ZesuSsz.Automation.SourceRegisterCodec203.
Require Import ZesuSsz.Automation.SourceRegisterOrigin194.
Require Import ZesuSsz.Automation.SourceWitnessInputs.
Require Import ZesuSsz.Evidence.EntryWitnessInputs.
Require Import isla.riscv64.riscv64.
Require Import isla.automation.
From iris.proofmode Require Import environments.

Ltac zesu_capture_source_register_post203 :=
  lazymatch goal with
  | |- envs_entails _
      (@zesu_source_register_post _ _ _ ?key ?width ?continuation ?value) =>
      is_closed_term width;
      EntryWitnessInputs.zesu_witness_resolved key;
      lazymatch value with
      | Val_Bits (@bv_to_bvn ?actual_width ?word) =>
          constr_eq actual_width width;
          EntryWitnessInputs.zesu_witness_resolved word;
          rewrite zesu_source_register_post_bits203;
          let name := iFresh in iIntros name;
          let marker := fresh "HsourceRegisterWitness" in
          pose (marker := @ZesuSourceWitnessHere (bv width) key word)
      end
  end.
