Require Import ZesuSsz.Automation.All.
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Contracts.Endpoints.
From ZesuSsz.Proofs.WriteSuccess Require Import
  Interfaces WriteSuccessNativeContract WriteSuccessRepresentation WriteSuccessValueBlock
  WriteSuccessExactValueSpec WriteSuccessExactValueLiveEntry.
Lemma write_success_exact_caller_equiv `{!islaG Sigma} `{!threadG}
    {Decoded} `{!WriteSuccessMemoryRepresentation Decoded}
    (args : WriteSuccessArgs Decoded) (witness : writeSuccessNativeWitness Decoded) :
  writeSuccessExactTailCaller args witness ⊣⊢
  writeSuccessExactValueLiveCaller (writeSuccessFrameSp witness)
    (writeSuccessValues witness) (writeSuccessPayload witness) (writeSuccessSourceBytes witness)
    (writeSuccessNativeStaticResources ∗ writeSuccessExactCallerRemainder args witness).
Proof.
  rewrite /writeSuccessExactTailCaller /writeSuccessExactValueLiveCaller
    /writeSuccessExactCallerRemainder /writeSuccessExactValueWord /writeSuccessValueWord.
  rewrite lookup_take; [|lia].
  iSplit.
  - iIntros "(Hlow & H104 & H280 & Hsource & Hvalues & H1624 & Hsaved & Hobject & Hpayload & Hraw & Hwithdrawals & Hpost & Hstatic & Hinvariant & Hwf & _)".
    iFrame.
  - iIntros "(H104 & H280 & Hsource & Hvalues & H1624 & Hpayload & Hcaller & _)".
    iDestruct "Hcaller" as "[Hstatic Hremainder]".
    iDestruct "Hremainder" as "(Hlow & Hsaved & Hobject & Hraw & Hwithdrawals & Hpost & Hinvariant & Hwf & _)".
    iFrame.
Qed.
Print Assumptions write_success_exact_caller_equiv.

Lemma write_success_exact_caller_equiv_framed `{!islaG Sigma} `{!threadG}
    {Decoded} `{!WriteSuccessMemoryRepresentation Decoded}
    (args : WriteSuccessArgs Decoded) (witness : writeSuccessNativeWitness Decoded)
    (P : iProp Sigma) :
  (writeSuccessExactTailCaller args witness ∗ P) ⊣⊢
  writeSuccessExactValueLiveCaller (writeSuccessFrameSp witness)
    (writeSuccessValues witness) (writeSuccessPayload witness) (writeSuccessSourceBytes witness)
    (writeSuccessNativeStaticResources ∗ writeSuccessExactCallerRemainder args witness ∗ P).
Proof.
  rewrite write_success_exact_caller_equiv /writeSuccessExactValueLiveCaller.
  iSplit.
  - iIntros "[(H104 & H280 & Hsource & Hvalues & H1624 & Hpayload & Hcaller & _) HP]".
    iDestruct "Hcaller" as "[Hstatic Hremainder]". iFrame.
  - iIntros "(H104 & H280 & Hsource & Hvalues & H1624 & Hpayload & Hcaller & _)".
    iDestruct "Hcaller" as "(Hstatic & Hremainder & HP)". iFrame.
Qed.
Print Assumptions write_success_exact_caller_equiv_framed.
