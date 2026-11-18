Require Import ZesuSsz.Automation.All.
Require Import ZesuSsz.Automation.EnvironmentIntroduction.
Require Import ZesuSsz.Evidence.Corrected69e8Complete419.
Require Import ZesuSsz.Generated.DecodeItem.MachineJoin698cEntries.

(* Fix the source before lookup.  The compiled entailment consumes the actual
   owned environment.  Remaining proof arguments come from existing facts. *)
#[global] Hint Extern 0
    (@ZesuPureFactIntro ?Sigma
      (@generatedJoin698c ?Sigma ?islaG ?threadG ?args ?returnAddress ?domain)
      (environments.of_envs ?environment)) =>
  (apply EnvironmentIntroduction.zesu_environment_intro;
   eapply Corrected69e8Complete419.corrected69e8_exact419;
   lazymatch goal with
   | |- ?condition =>
       let kind := type of condition in
       constr_eq kind Prop;
       eassumption
   end) : typeclass_instances.
