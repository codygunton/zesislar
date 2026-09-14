Require Import ZesuSsz.Automation.All.
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Contracts.Endpoints.
From ZesuSsz.Proofs.WriteSuccess Require Import
  Interfaces WriteSuccessNativeContract WriteSuccessRepresentation WriteSuccessValueBlock
  WriteSuccessExactValueSpec WriteSuccessExactCopiedValueLiveEntry.
Require Import ZesuSsz.Automation.All.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessExactCopiedHeaderCallerEquiv.
Lemma write_success_exact_copied_caller_equiv_framed `{!islaG Sigma} `{!threadG}
    {Decoded} `{!WriteSuccessMemoryRepresentation Decoded}
    (args : WriteSuccessArgs Decoded) (witness : writeSuccessNativeWitness Decoded)
    (P : iProp Sigma) :
  (writeSuccessExactTailCallerWithCopiedWords args witness ∗ P) ⊣⊢
  writeSuccessExactCopiedValueLiveCaller (writeSuccessFrameSp witness)
    (writeSuccessValues witness) (writeSuccessPayload witness) (writeSuccessSourceBytes witness) (writeSuccessDecodedBytes witness)
    (writeSuccessNativeStaticResources ∗ writeSuccessExactCallerRemainder args witness ∗ P).
Proof.
  rewrite write_success_exact_copied_caller_equiv /writeSuccessExactCopiedValueLiveCaller.
  iSplit.
  - iIntros "[(H8 & Hwords & Hsource & Hvalues & H1624 & Hpayload & Hcaller & _) HP]".
    iDestruct "Hcaller" as "[Hstatic Hremainder]". iFrame.
  - iIntros "(H8 & Hwords & Hsource & Hvalues & H1624 & Hpayload & Hcaller & _)".
    iDestruct "Hcaller" as "(Hstatic & Hremainder & HP)". iFrame.
Qed.
Print Assumptions write_success_exact_copied_caller_equiv_framed.
