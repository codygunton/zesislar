From Coq Require Import Lists.List ZArith.ZArith.
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Contracts.IslarisMemory.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessTransactionsSpec.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessTransactionsBoundary14f1c.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessTransactionsBoundary150e8.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessTransactionsBoundary150e8Phase.

Lemma write_success_transactions_at_150e8_phase_public
    `{!islaG Sigma} `{!threadG} (P : iProp Sigma) :
  writeSuccessTransactionsAt150e8PhaseSpec P -∗
  writeSuccessTransactionsAt150e8Spec P.
Proof.
  iIntros "Hentry".
  rewrite /writeSuccessTransactionsAt150e8PhaseSpec.
  iDestruct "Hentry" as
    (sp base transaction transactions processed remaining
      bytes prefix suffix tail)
    "(Hmachine & Hcurrent & Hframe & Hfacts & _)".
  iPoseProof "Hfacts" as "#HfactsCopy".
  iEval (unfold writeSuccessTransactionsLoadFacts) in "HfactsCopy".
  iDestruct "HfactsCopy" as "(%Hlength & _)".
  iEval (unfold writeSuccessTransactionsMachine150e8Phase) in "Hmachine".
  iDestruct "Hmachine" as "(Hsys & Hother & Hmachine)".
  iDestruct (reg_col_lookup writeSuccessTransactions150e8PhaseOtherRegShapes
    0%nat (KindReg "x1", BitsShape 64) with "Hother") as
    (ra HraShape) "(Hx1 & Hother)".
  { vm_compute. reflexivity. }
  destruct (valu_has_bits_shape ra 64 HraShape) as [raBits ->].
  iAssert (reg_col writeSuccessTransactions150e8OtherRegShapes)
    with "[Hother]" as "HotherFinal".
  { rewrite /writeSuccessTransactions150e8PhaseOtherRegShapes
      /writeSuccessTransactions150e8PhaseOtherRegisters
      /writeSuccessTransactions150e8OtherRegShapes
      /writeSuccessTransactions150e8OtherRegisters /=.
    iExact "Hother". }
  iAssert (writeSuccessTransactionsMachine150e8Rest
      sp base transactions processed transaction)
    with "[HotherFinal Hmachine]" as "HmachineFinal".
  { rewrite /writeSuccessTransactionsMachine150e8Rest.
    iFrame "HotherFinal Hmachine". }
  iEval (unfold writeSuccessTransactionsCurrentPhaseFrame) in "Hframe".
  iDestruct "Hframe" as
    "(Hprefix & HremainingBytes & Hprocessed & Hdata & HtransactionRest &
      Hremaining & Hmmio & Htrace & HP & Hinv & Hexit & _)".
  iPoseProof "Hinv" as "#HinvCopy".
  iPoseProof "HinvCopy" as "#HinvFinal".
  iEval (unfold WriteSuccessTransactionsSpec.writeSuccessTransactionsInvariant)
    in "HinvCopy".
  iDestruct "HinvCopy" as "(_ & _ & _ & %Hsuffix & _)".
  iPoseProof (mem_mapsto_array_app_combine_at 8%N
    (base + 288 * Z.of_nat (length processed)) (DfracOwn 1)
    (writeSuccessTransactionBytes transaction)
    (writeSuccessTransactionsBytes remaining) 288%nat Hlength
    with "Hcurrent HremainingBytes") as "HsuffixBytes".
  iAssert ((base + 288 * Z.of_nat (length processed)) ↦ₘ∗ suffix)%I
    with "[HsuffixBytes]" as "HsuffixFinal".
  { rewrite Hsuffix /=. iExact "HsuffixBytes". }
  iEval (unfold writeSuccessTransactionsProcessedOwn) in "Hprocessed".
  iAssert (writeSuccessTransactionOwn transaction)
    with "[Hdata HtransactionRest]" as "Htransaction".
  { rewrite /writeSuccessTransactionOwn /writeSuccessTransactionRestOwn.
    iFrame. }
  iEval (rewrite /writeSuccessTransactionPhaseEvents /=) in "Htrace".
  iExists sp, base, transaction, transactions, processed, remaining,
    bytes, prefix, suffix, tail, raBits.
  rewrite /writeSuccessTransactionsContext150e8.
  iFrame "Hsys Hx1 HmachineFinal Hprefix HsuffixFinal Hprocessed
    Htransaction Hremaining Hmmio Htrace HP HinvFinal Hexit".
Qed.
