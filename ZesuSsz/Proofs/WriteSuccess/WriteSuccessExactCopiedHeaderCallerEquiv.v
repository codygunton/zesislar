Require Import ZesuSsz.Automation.All.
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Contracts.Endpoints.
From ZesuSsz.Proofs.WriteSuccess Require Import
  Interfaces WriteSuccessNativeContract WriteSuccessRepresentation WriteSuccessValueBlock
  WriteSuccessExactValueSpec WriteSuccessExactCopiedValueLiveEntry.
Lemma write_success_exact_copied_caller_equiv `{!islaG Sigma} `{!threadG}
    {Decoded} `{!WriteSuccessMemoryRepresentation Decoded}
    (args : WriteSuccessArgs Decoded) (witness : writeSuccessNativeWitness Decoded) :
  writeSuccessExactTailCallerWithCopiedWords args witness ⊣⊢
  writeSuccessExactCopiedValueLiveCaller (writeSuccessFrameSp witness)
    (writeSuccessValues witness) (writeSuccessPayload witness) (writeSuccessSourceBytes witness) (writeSuccessDecodedBytes witness)
    (writeSuccessNativeStaticResources ∗ writeSuccessExactCallerRemainder args witness).
Proof.
  rewrite /writeSuccessExactTailCallerWithCopiedWords /writeSuccessExactCopiedValueLiveCaller
    /writeSuccessExactCallerRemainder /writeSuccessExactValueWord /writeSuccessValueWord.
  rewrite lookup_take; [|lia].
  iSplit.
  - iIntros "(Hlow & H8 & Hwords & Hsource & Hvalues & H1624 & Hsaved & Hobject & Hpayload & Hraw & Hwithdrawals & Hpost & Hstatic & Hinvariant & Hwf & _)".
    iFrame.
  - iIntros "(H8 & Hwords & Hsource & Hvalues & H1624 & Hpayload & Hcaller & _)".
    iDestruct "Hcaller" as "[Hstatic Hremainder]".
    iDestruct "Hremainder" as "(Hlow & Hsaved & Hobject & Hraw & Hwithdrawals & Hpost & Hinvariant & Hwf & _)".
    iFrame.
Qed.
Print Assumptions write_success_exact_copied_caller_equiv.

