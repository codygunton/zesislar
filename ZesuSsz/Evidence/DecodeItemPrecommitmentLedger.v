Require Import ZesuSsz.Automation.All.
Require Import ZesuSsz.Automation.Approved.
Require Import ZesuSsz.Compliance.DecodeItemHints.
From Coq Require Import List String ZArith.
Import ListNotations.
Open Scope string_scope.

(* The ledger records measured operations and failures. It does not assert native closure.
   MonitoredOperationRecorded does not establish a requested assignment boundary.
   Exact targets, contexts, scopes, and limits are bound in precommitment/LEDGER.json. *)
Inductive DecodeItemPrecommitmentStatus :=
| PrecommitmentUnknown
| ExplicitIntroductionApplied
| MonitoredOperationRecorded
| ArraySelectionRecorded
| CommittedSuccessorMismatch.

Record DecodeItemPrecommitmentRow := {
  precommitmentBlock : Z;
  precommitmentStatus : DecodeItemPrecommitmentStatus;
  precommitmentCandidate : string;
  precommitmentEvidence : string
}.

Definition decodeItemPrecommitmentLedger : list DecodeItemPrecommitmentRow := [
  {| precommitmentBlock := 0x800d6960%Z; precommitmentStatus := MonitoredOperationRecorded;
     precommitmentCandidate := "liExist; requested assignment unavailable"; precommitmentEvidence := "precommitment/LEDGER.json row 6960" |};
  {| precommitmentBlock := 0x800d697c%Z; precommitmentStatus := MonitoredOperationRecorded;
     precommitmentCandidate := "ZesuSsz.Automation.Hooks.zesu_pure_witness_constraints_if_enabled; requested assignment unavailable"; precommitmentEvidence := "precommitment/LEDGER.json row 697c" |};
  {| precommitmentBlock := 0x800d698c%Z; precommitmentStatus := ArraySelectionRecorded;
     precommitmentCandidate := "liFindInContext; index and updated-resource continuation remain"; precommitmentEvidence := "precommitment/LEDGER.json row 698c" |};
  {| precommitmentBlock := 0x800d69b0%Z; precommitmentStatus := ArraySelectionRecorded;
     precommitmentCandidate := "liFindInContext; index and updated-resource continuation remain"; precommitmentEvidence := "precommitment/LEDGER.json row 69b0" |};
  {| precommitmentBlock := 0x800d69e8%Z; precommitmentStatus := MonitoredOperationRecorded;
     precommitmentCandidate := "ZesuSsz.Automation.Hooks.zesu_pure_witness_constraints_if_enabled; requested assignment unavailable"; precommitmentEvidence := "precommitment/LEDGER.json row 69e8" |};
  {| precommitmentBlock := 0x800d6a08%Z; precommitmentStatus := ExplicitIntroductionApplied;
     precommitmentCandidate := "decodeItemStringSliceWitness"; precommitmentEvidence := "precommitment/LEDGER.json row 6a08" |};
  {| precommitmentBlock := 0x800d6a24%Z; precommitmentStatus := CommittedSuccessorMismatch;
     precommitmentCandidate := "S131 stepped i+1 certificate rejects committed i target"; precommitmentEvidence := "precommitment/LEDGER.json row 6a24" |};
  {| precommitmentBlock := 0x800d6a38%Z; precommitmentStatus := ExplicitIntroductionApplied;
     precommitmentCandidate := "decodeItemStringReturnLengthWitness"; precommitmentEvidence := "precommitment/LEDGER.json row 6a38" |};
  {| precommitmentBlock := 0x800d6a40%Z; precommitmentStatus := ArraySelectionRecorded;
     precommitmentCandidate := "liFindInContext; index and updated-resource continuation remain"; precommitmentEvidence := "precommitment/LEDGER.json row 6a40" |};
  {| precommitmentBlock := 0x800d6a78%Z; precommitmentStatus := ArraySelectionRecorded;
     precommitmentCandidate := "liFindInContext; index and updated-resource continuation remain"; precommitmentEvidence := "precommitment/LEDGER.json row 6a78" |};
  {| precommitmentBlock := 0x800d6aa8%Z; precommitmentStatus := ExplicitIntroductionApplied;
     precommitmentCandidate := "decodeItemListSliceWitness"; precommitmentEvidence := "precommitment/LEDGER.json row 6aa8" |};
  {| precommitmentBlock := 0x800d6ac4%Z; precommitmentStatus := CommittedSuccessorMismatch;
     precommitmentCandidate := "S131 stepped i+1 certificate rejects committed i target"; precommitmentEvidence := "precommitment/LEDGER.json row 6ac4" |};
  {| precommitmentBlock := 0x800d6ad8%Z; precommitmentStatus := ExplicitIntroductionApplied;
     precommitmentCandidate := "decodeItemListReturnLengthWitness"; precommitmentEvidence := "precommitment/LEDGER.json row 6ad8" |};
  {| precommitmentBlock := 0x800d6ae0%Z; precommitmentStatus := ArraySelectionRecorded;
     precommitmentCandidate := "liFindInContext; index and updated-resource continuation remain"; precommitmentEvidence := "precommitment/LEDGER.json row 6ae0" |};
  {| precommitmentBlock := 0x800d6b08%Z; precommitmentStatus := ArraySelectionRecorded;
     precommitmentCandidate := "liFindInContext; index and updated-resource continuation remain"; precommitmentEvidence := "precommitment/LEDGER.json row 6b08" |}
].

Definition decodeItemI67ResidualBlocks : list Z :=
  [0x800d6960; 0x800d697c; 0x800d698c; 0x800d69b0; 0x800d69e8; 0x800d6a08; 0x800d6a24; 0x800d6a38; 0x800d6a40; 0x800d6a78; 0x800d6aa8; 0x800d6ac4; 0x800d6ad8; 0x800d6ae0; 0x800d6b08]%Z.

Lemma decodeItemPrecommitmentLedger_inventory :
  map precommitmentBlock decodeItemPrecommitmentLedger = decodeItemI67ResidualBlocks.
Proof. reflexivity. Qed.

Lemma decodeItemPrecommitmentLedger_unique :
  NoDup (map precommitmentBlock decodeItemPrecommitmentLedger).
Proof. repeat constructor; simpl; intuition discriminate. Qed.

Lemma decodeItemPrecommitmentLedger_unknown_count :
  List.length (filter (fun row => match precommitmentStatus row with
    | PrecommitmentUnknown => true | _ => false end)
    decodeItemPrecommitmentLedger) = 0%nat.
Proof. reflexivity. Qed.

Lemma decodeItemPrecommitmentLedger_open_count :
  List.length decodeItemPrecommitmentLedger = 15%nat.
Proof. reflexivity. Qed.
