Require Import ZesuSsz.Automation.All.
Require Import ZesuSsz.Automation.Approved.
Require Import ZesuSsz.Compliance.DecodeItemHints.
Require Import ZesuSsz.Evidence.DecodeItemOpenNativeHypotheses.
Require Import ZesuSsz.Evidence.DecodeItemPrecommitmentWitnessFixtures.
From Coq Require Import List String ZArith.
Import ListNotations.
Open Scope string_scope.

(* This placeholder names the future switch. It does not activate a rule. *)
Class DecodeItemRouteRepairSwitchIdentity := {
  routeRepairSwitchModule : string;
  routeRepairSwitchClass : string;
  routeRepairSwitchInstance : string
}.

Definition decodeItemRouteRepairModule :=
  "ZesuSsz.Automation.Switches.ResourceFirstIntroduction".
Definition decodeItemRouteRepairClass := "ZesuStepResourceFirstIntroduction".
Definition decodeItemRouteRepairInstance := "zesu_switch_resource_first_introduction".

Definition decodeItemRouteRepairBlocks : list Z :=
  [0x800d6960; 0x800d697c; 0x800d69e8; 0x800d6a08; 0x800d6a38;
   0x800d6aa8; 0x800d6ad8; 0x800d6a24; 0x800d6ac4]%Z.

(* These are complete native block obligations, not pure witness certificates.
   No instance of this acceptance proposition is supplied before native proofs. *)
Definition decodeItemRouteRepairNativeObligations : list Prop :=
  [decodeItemOpenNativeClosure6960; decodeItemOpenNativeClosure697c;
   decodeItemOpenNativeClosure69e8; decodeItemOpenNativeClosure6a08;
   decodeItemOpenNativeClosure6a38; decodeItemOpenNativeClosure6aa8;
   decodeItemOpenNativeClosure6ad8; decodeItemOpenNativeClosure6a24;
   decodeItemOpenNativeClosure6ac4].

Definition DecodeItemRouteRepairAcceptance `{DecodeItemRouteRepairSwitchIdentity} : Prop :=
  routeRepairSwitchModule = decodeItemRouteRepairModule /\
  routeRepairSwitchClass = decodeItemRouteRepairClass /\
  routeRepairSwitchInstance = decodeItemRouteRepairInstance /\
  Forall (fun obligation : Prop => obligation) decodeItemRouteRepairNativeObligations.

Definition decodeItemRouteRepairRejectLiteral := s119_literal_committed_witness_conflict.
Definition decodeItemRouteRepairRejectSuccessor := s119_successor_committed_witness_conflict.

Lemma decodeItemRouteRepairAcceptance_count :
  List.length decodeItemRouteRepairBlocks = 9%nat /\
  List.length decodeItemRouteRepairNativeObligations = 9%nat.
Proof. split; reflexivity. Qed.

Lemma decodeItemRouteRepairAcceptance_unique : NoDup decodeItemRouteRepairBlocks.
Proof. repeat constructor; simpl; intuition discriminate. Qed.

Print Assumptions decodeItemRouteRepairAcceptance_count.
Print Assumptions decodeItemRouteRepairAcceptance_unique.
Print Assumptions decodeItemRouteRepairRejectLiteral.
Print Assumptions decodeItemRouteRepairRejectSuccessor.
