Require Import ZesuSsz.Automation.All.
Require Import ZesuMachineMap.Machine.
From Coq Require Import Lists.List ZArith.ZArith.
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessTransactionsSpec.

Lemma write_success_transactions_access_transaction_invariant
    `{!islaG Sigma} (sp : bv 64) (base : Z)
    (transactions processed remaining : list writeSuccessTransaction)
    (bytes prefix suffix : list (bv 8)) :
  writeSuccessTransactionsInvariant sp base transactions processed
    remaining bytes prefix suffix -∗
  ⌜bv_unsigned sp `mod` 16 = 0⌝ ∗
  ⌜(mapRamBase defaultMap) <= bv_unsigned sp - 48⌝ ∗
  ⌜bv_unsigned sp + 1896 < (machineRamEnd defaultMap)⌝ ∗
  writeSuccessTransactionsInvariant sp base transactions processed
    remaining bytes prefix suffix.
Proof.
  iIntros "Hinvariant".
  iEval (rewrite /writeSuccessTransactionsInvariant) in "Hinvariant".
  iDestruct "Hinvariant" as
    "(HtransactionsEq & HbytesEq & HprefixEq & HsuffixEq & HbytesAppend &
      HbytesLength & HprefixLength & HsuffixLength & HtransactionsBound &
      %HspAlign & %HspLow & %HspHigh & HbaseAlign & HbaseLow & HbaseHigh & _)".
  iAssert (writeSuccessTransactionsInvariant sp base transactions processed
      remaining bytes prefix suffix)%I
    with "[HtransactionsEq HbytesEq HprefixEq HsuffixEq HbytesAppend
      HbytesLength HprefixLength HsuffixLength HtransactionsBound HbaseAlign
      HbaseLow HbaseHigh]" as "Hinvariant".
  { rewrite /writeSuccessTransactionsInvariant.
    iFrame "HtransactionsEq HbytesEq HprefixEq HsuffixEq HbytesAppend
      HbytesLength HprefixLength HsuffixLength HtransactionsBound HbaseAlign
      HbaseLow HbaseHigh".
    repeat iSplit; try iPureIntro; try assumption; done. }
  iSplit; [iPureIntro; exact HspAlign|].
  iSplit; [iPureIntro; exact HspLow|].
  iSplit; [iPureIntro; exact HspHigh|].
  iExact "Hinvariant".
Qed.
