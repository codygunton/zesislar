Require Import ZesuSsz.Compliance.DecodeItemCompliance.
Require Import ZesuSsz.Compliance.DecodeItemComplianceGenerated.

(* The theorem over the generated block proofs has the reviewed type of the
   production compliance theorem. *)
Definition decodeItemGeneratedComplianceReviewed :
  ZesuSsz.Compliance.DecodeItemCompliance.ReviewedDecodeItemComplianceType :=
  ZesuSsz.Compliance.DecodeItemComplianceGenerated.decodeItemGeneratedCompliance.

Print Assumptions ZesuSsz.Compliance.DecodeItemComplianceGenerated.decodeItemGeneratedCompliance.
