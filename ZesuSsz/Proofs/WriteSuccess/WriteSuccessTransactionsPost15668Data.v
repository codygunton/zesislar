Require Import ZesuSsz.Automation.AllLegacy.
Require Import isla.riscv64.riscv64.
From IslaTraces.write_success_blocks Require Import Index.
Require Import ZesuSsz.Contracts.IslarisCode.
Require Import ZesuSsz.Contracts.IslarisMachine.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessTransactionsLoopExitEvents.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessTransactionsPuncturedScratch.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessTransactionsPost15668DataStates.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessTransactionsPost15674Boundary.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessTransactionsPostWithdrawalsData.
Require Import IslaTraces.write_success_87.a15668_spec.

Local Remove Hints subsume_instr_pre'_inst : typeclass_instances.
Local Existing Instance subsume_instr_pre_wand_inst | 1.

Lemma write_success_transactions_post_15668_data
    `{!islaG Sigma} `{!threadG} (P : iProp Sigma) :
  instr_lookup_resources IslaTraces.write_success_blocks.Index.lookup -∗
  instr_body 0x1566c (writeSuccessTransactionsPost1566cDataSpec P) -∗
  instr_body 0x15668 (writeSuccessTransactionsPostAt15668DataSpec P).
Proof.
  iStartProof. iIntros "#Hlookup Hnext".
  iPoseProof "Hlookup" as "#Hlookup15668".
  iEval (rewrite /instr_lookup_resources) in "Hlookup15668".
  iPoseProof ("Hlookup15668" $! 0x15668 with "[]") as "#Hinstr15668".
  { iPureIntro. rewrite IslaTraces.write_success_blocks.Index.lookup_a15668. done. }
  iPoseProof (IslaTraces.write_success_87.a15668_spec.a15668_spec
    0x15668 with "Hinstr15668") as "Hld".
  rewrite instr_pre'_eq. iIntros "Hentry".
  iEval (rewrite /writeSuccessTransactionsPostAt15668DataSpec
    /writeSuccessTransactionsLoopExitWithdrawalsData
    /writeSuccessTransactionsLoopExitEventsData) in "Hentry".
  iDestruct "Hentry" as
    (sp pointer base transactions bytes tail remaining first second items)
    "(Hsys & Hother & H2 & H10 & H11 & Harray & Hown & Hscratch &
      Hcarrier & Hwithdrawals & Hmmio & Htrace & %Halign16 & %Halign8 &
      %Hlow & %Hhigh & HP & _)".
  iEval (rewrite /writeSuccessTransactionsLoopCarrierPayload
    /writeSuccessTransactionsWordsCarrier) in "Hcarrier".
  iDestruct "Hcarrier" as
    "((Hfirst & Hsecond & Hpointer & Hremaining) & HcallStack & Hitems & %Hfacts)".
  destruct Hfacts as
    (HsecondLength & HitemsLength & HfirstAlign & HfirstLower & HfirstUpper &
     HspExtract & HspCallLower & HspMax).
  pose proof HspExtract as HspExtractOriginal.
  bv_simplify HspExtract.
  iAssert ("x10" ↦ᵣ: fun _ => True)%I with "[H10]" as "H10Any".
  { rewrite reg_mapsto_pred_eq /reg_mapsto_pred_def. iExists _. iFrame. }
  rewrite /InstrSpecs.Specs.zesu_ld_spec /InstrSpecs.Specs.rv64_ld_spec.
  iApply "Hld". iExists first, sp. iFrame "Hsys H10Any H2 Hfirst".
  repeat iSplit; try iPureIntro; try assumption; try bv_solve; try lia.
  rewrite instr_pre'_eq. iNext. iIntros "Hpost".
  iApply "Hnext".
  iEval (rewrite /writeSuccessTransactionsPost1566cDataSpec).
  iExists sp, pointer, base, transactions, bytes, tail, remaining, first, second,
    items.
  iDestruct "Hpost" as "(HsysPost & H10Post & H2Post & HfirstPost & _)".
  iFrame "HsysPost Hother H2Post H10Post H11 Harray Hown Hscratch Hwithdrawals
    Hmmio Htrace HP".
  rewrite /writeSuccessTransactionsLoopCarrierPayload
    /writeSuccessTransactionsWordsCarrier.
  iFrame "HfirstPost Hsecond Hpointer Hremaining HcallStack Hitems".
  iSplit.
  { iPureIntro. repeat split; assumption. }
  repeat iSplit; try iPureIntro; try assumption; try done.
Qed.
