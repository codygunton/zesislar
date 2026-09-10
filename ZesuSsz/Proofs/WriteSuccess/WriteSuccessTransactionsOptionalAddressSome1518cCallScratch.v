From Coq Require Import Lists.List ZArith.ZArith.
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Contracts.IslarisMachine.
Require Import ZesuSsz.Experiments.WriteSuccessTransactionsOptionalAddressSome1517cBoundary.
Require Import ZesuSsz.Experiments.WriteSuccessTransactionsOptionalAddressSome15190Boundary.
Require Import ZesuSsz.Experiments.WriteSuccessTransactionsOptionalAddressSome15170Handoff.
Require Import ZesuSsz.Experiments.WriteSuccessTransactionsSpec.

Lemma write_success_transactions_optional_address_some_1518c_call_scratch
    `{!islaG Sigma} `{!threadG} (P : iProp Sigma)
    (sp : bv 64) (base : Z) (transaction : writeSuccessTransaction)
    (transactions processed remaining : list writeSuccessTransaction)
    (bytes prefix suffix : list (bv 8)) (tail : spec) :
  reg_col [(KindReg "x3", BitsShape 64); (KindReg "x4", BitsShape 64)] ∗
  writeSuccessTransactionsScratch15174
    sp base transactions processed transaction ∗
  writeSuccessTransactionsOptionalAddressSomeFrame P sp base transaction
    transactions processed remaining bytes prefix suffix tail -∗
  writeSuccessTransactionsOptionalAddressSome15190Frame P sp base transaction
    transactions processed remaining bytes prefix suffix tail ∗
  ⌜bv_unsigned sp `mod` 16 = 0⌝ ∗
  ⌜0x20000000 <= bv_unsigned sp - 16⌝ ∗
  ⌜bv_unsigned sp < 0x40000000⌝.
Proof.
  iIntros "(H34 & Hscratch & Hframe)".
  iEval (unfold writeSuccessTransactionsOptionalAddressSomeFrame) in "Hframe".
  iDestruct "Hframe" as
    "(Hprefix & Hsuffix & Hprocessed & Htransaction & Hremaining & HP & Hinv &
      Hexit & %Hto & _)".
  iDestruct "Hinv" as "#Hinv".
  iPoseProof "Hinv" as "#HinvCopy".
  iEval (unfold writeSuccessTransactionsInvariant) in "HinvCopy".
  do 9 (iDestruct "HinvCopy" as "[_ HinvCopy]").
  iDestruct "HinvCopy" as "[HspAlign HinvCopy]".
  iDestruct "HinvCopy" as "[HspLower HinvCopy]".
  iDestruct "HinvCopy" as "[HspUpper _]".
  iDestruct "HspAlign" as "%Halign".
  iDestruct "HspLower" as "%Hlower".
  iDestruct "HspUpper" as "%Hupper".
  iAssert (writeSuccessTransactionsOptionalAddressSomeFrame P sp base transaction
    transactions processed remaining bytes prefix suffix tail)%I
    with "[Hprefix Hsuffix Hprocessed Htransaction Hremaining HP Hinv Hexit]"
    as "Hframe".
  { rewrite /writeSuccessTransactionsOptionalAddressSomeFrame.
    iFrame "Hprefix Hsuffix Hprocessed Htransaction Hremaining HP Hinv Hexit".
    iSplit; [iPureIntro; exact Hto | done]. }
  iAssert (writeSuccessTransactionsOptionalAddressSome15190Frame P sp base
    transaction transactions processed remaining bytes prefix suffix tail)%I
    with "[H34 Hscratch Hframe]" as "Hframe15190".
  { rewrite /writeSuccessTransactionsOptionalAddressSome15190Frame.
    iFrame "H34 Hscratch Hframe"; done. }
  have HstackLower : (0x20000000 <= bv_unsigned sp - 16)%Z by lia.
  have HstackUpper : (bv_unsigned sp < 0x40000000)%Z by lia.
  iFrame "Hframe15190".
  iPureIntro. split; [exact Halign |]. split; [exact HstackLower | exact HstackUpper].
Qed.
