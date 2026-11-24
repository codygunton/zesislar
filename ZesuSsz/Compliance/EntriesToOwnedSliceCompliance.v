(* entriesToOwnedSlice compliance (plan B3): every block of the region is closed,
   so the composition over the block table needs no premise. *)
Require Import ZesuSsz.Contracts.EntriesToOwnedSliceContract.
Require Import ZesuSsz.Compliance.EntriesToOwnedSliceBlockObligations.
Require Import ZesuSsz.Compliance.EntriesToOwnedSliceGeneratedComposition.

Theorem entriesToOwnedSliceCompliance : EntriesToOwnedSliceContractCorrect.
Proof. exact (entriesToOwnedSliceGeneratedCompliance entriesToOwnedSliceOpenBlocks). Qed.
