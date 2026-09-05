From Coq Require Import Lists.List ZArith.ZArith.
Require Import isla.riscv64.riscv64.
From IslaTraces.write_success_blocks Require Import Index.
Require Import ZesuSsz.Contracts.IslarisCode.
Require Import ZesuSsz.Experiments.WriteSuccessTransactionsWithdrawalsTotalIntProvider.
Require Import ZesuSsz.Experiments.WriteSuccessTransactionsWithdrawalsTotalTailState.

#[local] Hint Extern 7
  (FindInContext (FindInstrKind ?address ?later) FICSyntactic) =>
  let reduced := eval vm_compute in address in
  first [ constr_eq address reduced; fail 1
        | change (FindInContext (FindInstrKind reduced later) FICSyntactic);
          typeclasses eauto ] : typeclass_instances.

Lemma write_success_transactions_withdrawals_total_tail_call
    `{!islaG Sigma} `{!threadG} (P : iProp Sigma) :
  instr_lookup_resources IslaTraces.write_success_blocks.Index.lookup -∗
  instr_pre 0x15d10
    (writeSuccessTransactionsWithdrawalsTotalIntEntrySpec P) -∗
  instr_body 0x15680
    (writeSuccessTransactionsWithdrawalsTotalAt15680Spec P).
Proof.
  iStartProof. iIntros "#Hlookup HintProvider".
  iPoseProof "Hlookup" as "#Hlookup15680".
  iEval (rewrite /instr_lookup_resources) in "Hlookup15680".
  iPoseProof ("Hlookup15680" $! 0x15680 with "[]") as "#Hinstr15680".
  { iPureIntro. rewrite IslaTraces.write_success_blocks.Index.lookup_a15680. done. }
  iEval (rewrite IslaTraces.write_success_blocks.Index.lookup_a15680)
    in "Hinstr15680".
  iPoseProof "Hlookup" as "#Hlookup15684".
  iEval (rewrite /instr_lookup_resources) in "Hlookup15684".
  iPoseProof ("Hlookup15684" $! 0x15684 with "[]") as "#Hinstr15684".
  { iPureIntro. rewrite IslaTraces.write_success_blocks.Index.lookup_a15684. done. }
  iEval (rewrite IslaTraces.write_success_blocks.Index.lookup_a15684)
    in "Hinstr15684".
  iPoseProof "Hlookup" as "#Hlookup15688".
  iEval (rewrite /instr_lookup_resources) in "Hlookup15688".
  iPoseProof ("Hlookup15688" $! 0x15688 with "[]") as "#Hinstr15688".
  { iPureIntro. rewrite IslaTraces.write_success_blocks.Index.lookup_a15688. done. }
  iEval (rewrite IslaTraces.write_success_blocks.Index.lookup_a15688)
    in "Hinstr15688".
  iClear "Hlookup Hlookup15680 Hlookup15684 Hlookup15688".
  rewrite instr_pre'_eq. iIntros "Hentry".
  iEval (rewrite /writeSuccessTransactionsWithdrawalsTotalAt15680Spec) in "Hentry".
  iDestruct "Hentry" as (sp pointer base count bytes tail)
    "(Hsys & H2 & H8 & H9 & Hframe)".
  iEval (rewrite /writeSuccessTransactionsWithdrawalsTotalTailFrame) in "Hframe".
  iDestruct "Hframe" as
    "(Hpreserved & H1 & H5 & H10 & H11 & H18 & HcallScratch & HpointerWord &
      HcountWord & HupperScratch & Hmmio & Htrace & %Halign & %Hlower & %Hupper &
      Hresources & _)".
  iEval (rewrite reg_mapsto_pred_eq /reg_mapsto_pred_def) in "H1".
  iDestruct "H1" as (r1) "(H1 & _)".
  iEval (rewrite reg_mapsto_pred_eq /reg_mapsto_pred_def) in "H10".
  iDestruct "H10" as (r10) "(H10 & _)".
  iEval (rewrite -instr_pre'_eq) in "HintProvider".
  replace (bv_wrap 64 87680) with 87680 by bv_solve.
  liARun.
  Unshelve. all: prepare_sidecond.
  all: try assumption.
  all: try bv_solve.
  all: try lia.
  Unshelve.
  iExists (tail, bytes, base, tt)ₗ.
  iSplit; first (iPureIntro; reflexivity).
  iSplit; first (iPureIntro; exact Halign).
  iSplit; first (iPureIntro; exact Hlower).
  iSplit; first (iPureIntro; lia).
  iSplit; last done.
  iExact "Hresources".
Qed.
