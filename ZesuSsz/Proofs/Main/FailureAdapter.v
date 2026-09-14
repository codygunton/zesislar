Require Import ZesuSsz.Automation.All.
Require Import ZesuSsz.Proofs.WriteFailure.TraceContract.

Definition mainFailurePrefixInstrs := writeFailureFramedPrefixInstrs.
Definition mainFailureTraceEntry := @writeFailureFramedTraceEntry.
Definition mainFailureTraceExit := @writeFailureFramedTraceExit.

Arguments mainFailureTraceEntry {_ _ _} _ _.
Arguments mainFailureTraceExit {_ _ _} _ _.
