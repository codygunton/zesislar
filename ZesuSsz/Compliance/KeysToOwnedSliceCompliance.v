(* keysToOwnedSlice compliance (plan B2): every block of the region is closed,
   so the composition over the block table needs no premise. *)
Require Import ZesuSsz.Contracts.KeysToOwnedSliceContract.
Require Import ZesuSsz.Compliance.KeysToOwnedSliceBlockObligations.
Require Import ZesuSsz.Compliance.KeysToOwnedSliceGeneratedComposition.

Theorem keysToOwnedSliceCompliance : KeysToOwnedSliceContractCorrect.
Proof. exact (keysToOwnedSliceGeneratedCompliance keysToOwnedSliceOpenBlocks). Qed.
