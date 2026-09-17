Require Import ZesuSsz.Automation.All.
Require Import isla.riscv64.riscv64.
Require Import InstrSpecs.Machine.
Require Import ZesuSsz.Contracts.Endpoints.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessRepresentation.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessNativeContract.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessValueSpec.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessExactEncoderIntFramedCall.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessExactTailWithdrawalCountModel.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessExactTailWithdrawalCountSpec.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessExactTailWithdrawalsBranchSpec.

Lemma folded_count_frame_first_resource `{!islaG Sigma} `{!threadG}
    {Decoded} `{!WriteSuccessMemoryRepresentation Decoded}
    (args : WriteSuccessArgs Decoded)
    (witness : writeSuccessNativeWitness Decoded)
    (P : iProp Sigma) :
  exactTailWithdrawalCountFrame args witness P -∗
  reg_col exactTailWithdrawalCountOtherCallerShapes ∗ True.
Proof.
  iStartProof. iIntros "Hframe".
  iEval (rewrite exactTailWithdrawalCountFrame_unfold
    /exactTailWithdrawalCommonFrame) in "Hframe".
  iDestruct "Hframe" as "(Hcaller & _)". iFrame.
Qed.
Print Assumptions folded_count_frame_first_resource.

Lemma folded_branch_sys_and_saved_x9 `{!islaG Sigma} `{!threadG}
    {Decoded} `{!WriteSuccessMemoryRepresentation Decoded}
    (args : WriteSuccessArgs Decoded)
    (witness : writeSuccessNativeWitness Decoded)
    (P : iProp Sigma) :
  exactTailWithdrawalBranchResources args witness P -∗
  reg_col zesu_ram_sys_regs ∗
  "x9" ↦ᵣ RVal_Bits
    (writeSuccessValueWord (writeSuccessValues witness) 12) ∗ True.
Proof.
  iStartProof. iIntros "Hbranch".
  iEval (rewrite /exactTailWithdrawalBranchResources
    /encoderIntExactFramedPost /exactTailWithdrawalBranchFrame
    /exactTailWithdrawalCommonFrame) in "Hbranch".
  zesu_open_resource_groups.
  zesu_run.
Qed.
Print Assumptions folded_branch_sys_and_saved_x9.
