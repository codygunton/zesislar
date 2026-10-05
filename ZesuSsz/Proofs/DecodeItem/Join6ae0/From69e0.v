Require Import ZesuSsz.Automation.All.
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Contracts.RlpDecodeItemContract.
Require Import ZesuSsz.Contracts.DecodeItemSelected.
Require Import ZesuSsz.Contracts.RlpDecodeItemJoinTransfers.
Require Import ZesuSsz.Proofs.DecodeItem.Join6ae0.Mask.
Require Import ZesuSsz.Proofs.DecodeItem.Join6ae0.Branch.

Lemma decodeItemJoin6ae0From69e0_correct `{!islaG Sigma} `{!threadG}
    args (frameBytes : list byte) (lengthRegister : bv 64)
    (inputPrefix : byte) (rest : list byte) :
  ⊢ decodeItemJoin6ae0From69e0 args frameBytes lengthRegister inputPrefix rest.
Proof.
  unfold decodeItemJoin6ae0From69e0, decodeItemJoinTransferObligation.
  iIntros "Hcode".
  iEval (unfold decodeItemSelectedCode) in "Hcode".
  iDestruct "Hcode" as "#Hcode".
  iPoseProof (decodeItemErrorMaskBridge_correct args frameBytes lengthRegister inputPrefix rest) as "Hmask".
  iEval (unfold decodeItemJoinTransferObligation, decodeItemSelectedCode)
    in "Hmask".
  iSpecialize ("Hmask" with "Hcode").
  iApply (instr_pre_wand with "Hmask"); [done | done |].
  iIntros "(Hsource & Hfinal & _)".
  iFrame "Hsource".
  iSplitL "Hfinal"; last done.
  iPoseProof (decodeItemErrorBranchBridge_correct args frameBytes
    (bv_and lengthRegister 127) inputPrefix rest) as "Hbranch".
  iEval (unfold decodeItemJoinTransferObligation, decodeItemSelectedCode)
    in "Hbranch".
  iSpecialize ("Hbranch" with "Hcode").
  iApply (instr_pre_wand with "Hbranch"); [done | done |].
  iIntros "[Hmid _]". iFrame.
Qed.

Print Assumptions decodeItemJoin6ae0From69e0_correct.
