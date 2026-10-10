Require Import ZesuSsz.Automation.All.
Require Import ZesuSsz.Automation.Approved.
Require Import ZesuSsz.Compliance.DecodeItemHints.
From Coq Require Import List String ZArith.
Import ListNotations.
Open Scope string_scope.

(* The ledger records measured applications. It does not assert native closure. *)
Inductive DecodeItemPrecommitmentStatus :=
| PrecommitmentUnknown
| ExplicitIntroductionApplied.

Record DecodeItemPrecommitmentRow := {
  precommitmentBlock : Z;
  precommitmentStatus : DecodeItemPrecommitmentStatus;
  precommitmentCandidate : string;
  precommitmentEvidence : string
}.

Definition decodeItemPrecommitmentLedger : list DecodeItemPrecommitmentRow := [
  {| precommitmentBlock := 0x800d6960%Z; precommitmentStatus := PrecommitmentUnknown;
     precommitmentCandidate := "S84 candidate; measured precommitment state unavailable"; precommitmentEvidence := "Typed precommitment capture unavailable" |};
  {| precommitmentBlock := 0x800d698c%Z; precommitmentStatus := PrecommitmentUnknown;
     precommitmentCandidate := ""; precommitmentEvidence := "Typed precommitment capture unavailable" |};
  {| precommitmentBlock := 0x800d69b0%Z; precommitmentStatus := PrecommitmentUnknown;
     precommitmentCandidate := ""; precommitmentEvidence := "Typed precommitment capture unavailable" |};
  {| precommitmentBlock := 0x800d6a08%Z; precommitmentStatus := ExplicitIntroductionApplied;
     precommitmentCandidate := "decodeItemStringSliceWitness"; precommitmentEvidence := "S117 EXPLICIT-S43-005 state337; FoldInitResources source remains open" |};
  {| precommitmentBlock := 0x800d6a24%Z; precommitmentStatus := PrecommitmentUnknown;
     precommitmentCandidate := ""; precommitmentEvidence := "Typed precommitment capture unavailable" |};
  {| precommitmentBlock := 0x800d6a38%Z; precommitmentStatus := ExplicitIntroductionApplied;
     precommitmentCandidate := "decodeItemStringReturnLengthWitness"; precommitmentEvidence := "S115 PRECOMMIT005 state31; FoldCheckedResources source remains open" |};
  {| precommitmentBlock := 0x800d6a40%Z; precommitmentStatus := PrecommitmentUnknown;
     precommitmentCandidate := ""; precommitmentEvidence := "Typed precommitment capture unavailable" |};
  {| precommitmentBlock := 0x800d6a78%Z; precommitmentStatus := PrecommitmentUnknown;
     precommitmentCandidate := ""; precommitmentEvidence := "Typed precommitment capture unavailable" |};
  {| precommitmentBlock := 0x800d6aa8%Z; precommitmentStatus := ExplicitIntroductionApplied;
     precommitmentCandidate := "decodeItemListSliceWitness"; precommitmentEvidence := "S117 EXPLICIT-S43-005 state674; FoldInitResources source remains open" |};
  {| precommitmentBlock := 0x800d6ad8%Z; precommitmentStatus := ExplicitIntroductionApplied;
     precommitmentCandidate := "decodeItemListReturnLengthWitness"; precommitmentEvidence := "S115 PRECOMMIT005 state79; FoldCheckedResources source remains open" |};
  {| precommitmentBlock := 0x800d6ac4%Z; precommitmentStatus := PrecommitmentUnknown;
     precommitmentCandidate := ""; precommitmentEvidence := "Typed precommitment capture unavailable" |};
  {| precommitmentBlock := 0x800d6ae0%Z; precommitmentStatus := PrecommitmentUnknown;
     precommitmentCandidate := ""; precommitmentEvidence := "Typed precommitment capture unavailable" |};
  {| precommitmentBlock := 0x800d6b08%Z; precommitmentStatus := PrecommitmentUnknown;
     precommitmentCandidate := ""; precommitmentEvidence := "Typed precommitment capture unavailable" |}
].

Definition decodeItemI67ResidualBlocks : list Z :=
  [0x800d6960; 0x800d698c; 0x800d69b0; 0x800d6a08; 0x800d6a24;
   0x800d6a38; 0x800d6a40; 0x800d6a78; 0x800d6aa8; 0x800d6ad8;
   0x800d6ac4; 0x800d6ae0; 0x800d6b08]%Z.

Lemma decodeItemPrecommitmentLedger_inventory :
  map precommitmentBlock decodeItemPrecommitmentLedger = decodeItemI67ResidualBlocks.
Proof. reflexivity. Qed.

Lemma decodeItemPrecommitmentLedger_unique :
  NoDup (map precommitmentBlock decodeItemPrecommitmentLedger).
Proof. repeat constructor; simpl; intuition discriminate. Qed.

Lemma decodeItemPrecommitmentLedger_unknown_count :
  List.length (filter (fun row => match precommitmentStatus row with
    | PrecommitmentUnknown => true | ExplicitIntroductionApplied => false end)
    decodeItemPrecommitmentLedger) = 9%nat.
Proof. reflexivity. Qed.
