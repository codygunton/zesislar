From Coq Require Import ZArith.ZArith.
Require Import isla.riscv64.riscv64.
From IslaTraces.write_success_blocks Require Import Index.
Require Import ZesuSsz.Contracts.IslarisCode.
Require Import ZesuSsz.Experiments.WriteSuccessTransactionsPost15690.
Require Import ZesuSsz.Experiments.WriteSuccessTransactionsPostWithdrawalsHandoff.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsSpec.

Lemma write_success_transactions_post_15690_withdrawals
    `{!islaG Sigma} `{!threadG} (P : iProp Sigma) :
  instr_lookup_resources IslaTraces.write_success_blocks.Index.lookup -∗
  □ instr_pre 0x15694 (writeSuccessTransactionsPostWithdrawalsHandoff P) -∗
  instr_body 0x15690 (writeSuccessTransactionsPostWithdrawalsHandoff P).
Proof.
  iStartProof. iIntros "#Hlookup #Hloop".
  iPoseProof "Hlookup" as "#Hlookup15690".
  iEval (rewrite /instr_lookup_resources) in "Hlookup15690".
  iPoseProof ("Hlookup15690" $! 0x15690 with "[]") as "#Hinstr15690".
  { iPureIntro.
    rewrite IslaTraces.write_success_blocks.Index.lookup_a15690.
    done. }
  iEval (rewrite IslaTraces.write_success_blocks.Index.lookup_a15690)
    in "Hinstr15690".
  iPoseProof (write_success_transactions_post_15690_nonzero_spec
    with "Hinstr15690") as "HnonzeroSpec".
  rewrite instr_pre'_eq. iIntros "Hentry".
  iEval (rewrite /writeSuccessTransactionsPostWithdrawalsHandoff
    /writeSuccessWithdrawalsLoopSpec) in "Hentry".
  iDestruct "Hentry" as
    (sp pointer base total processed remaining bytes prefix suffix tail)
    "(Hsys & Hother & H2 & H8 & H9 & H18 & Hprefix & Hsuffix & Hscratch &
      Hmmio & Htrace & HP & Hinv & Hexit & _)".
  iDestruct "Hinv" as
    "(%Htotal & %Hbytes & %Hconcat & %HprefixLength & %HsuffixLength &
      %Hpointer & %Hbound & %HspAlign & %HspLower & %HspUpper & %HbaseLower &
      %HbaseUpper & _)".
  have Hnonzero := write_success_withdrawals_remaining_nonzero remaining Hbound.
  iAssert (writeSuccessWithdrawalsInvariant sp pointer base total processed
    remaining bytes prefix suffix)%I with "[]" as "Hinv".
  { iPureIntro. repeat split; assumption. }
  iEval (rewrite /writeSuccessTransactionsPost15690NonzeroSpec).
  iApply "HnonzeroSpec".
  iExists (Z_to_bv 64 (Z.of_nat (S remaining))).
  iFrame "Hsys H9".
  iSplit.
  { iPureIntro. exact Hnonzero. }
  iEval (rewrite -instr_pre'_eq) in "Hloop".
  iApply (instr_pre_wand 0x15694 0x15694 true true with "Hloop");
    [done | done |].
  iIntros "Hpost".
  iDestruct "Hpost" as "(Hsys & H9 & _)".
  iEval (rewrite /writeSuccessTransactionsPostWithdrawalsHandoff
    /writeSuccessWithdrawalsLoopSpec).
  iExists sp, pointer, base, total, processed, remaining, bytes, prefix,
    suffix, tail.
  iFrame "Hsys Hother H2 H8 H9 H18 Hprefix Hsuffix Hscratch Hmmio Htrace HP
    Hinv Hexit".
Qed.
