Require Import ZesuSsz.Automation.All.
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Contracts.Endpoints.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessExactTailWithdrawalCountSpec.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessExactTailWithdrawalCountModel.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessExactEncoderIntFramedCall.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessRepresentation.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessNativeContract.
Open Scope Z_scope.

Definition exactTailWithdrawalBranchResources `{!islaG Sigma} `{!threadG}
    {Decoded} `{!WriteSuccessMemoryRepresentation Decoded}
    (args : WriteSuccessArgs Decoded) (witness : writeSuccessNativeWitness Decoded)
    (P : iProp Sigma) : iProp Sigma :=
  (encoderIntExactFramedPost (writeSuccessFrameSp witness) (BV 64 0x1568c)
     (exactTailAfterWithdrawalCountEvents witness)
     (exactTailWithdrawalBranchFrame args witness P) ∗
   "x18" ↦ᵣ RVal_Bits (writeSuccessFrameSp witness + BV 64 1768)%bv)%I.

Definition exactTailWithdrawalsBranchNonzeroEntry `{!islaG Sigma} `{!threadG}
    {Decoded} `{!WriteSuccessMemoryRepresentation Decoded}
    (args : WriteSuccessArgs Decoded) (witness : writeSuccessNativeWitness Decoded)
    (P : iProp Sigma) : iProp Sigma :=
  (exactTailWithdrawalBranchResources args witness P ∗
   ⌜0 < writeSuccessWithdrawalsCount witness⌝)%I.

Definition exactTailWithdrawalsBranchZeroEntry `{!islaG Sigma} `{!threadG}
    {Decoded} `{!WriteSuccessMemoryRepresentation Decoded}
    (args : WriteSuccessArgs Decoded) (witness : writeSuccessNativeWitness Decoded)
    (P : iProp Sigma) : iProp Sigma :=
  (exactTailWithdrawalBranchResources args witness P ∗
   ⌜writeSuccessWithdrawalsCount witness = 0%nat⌝)%I.
