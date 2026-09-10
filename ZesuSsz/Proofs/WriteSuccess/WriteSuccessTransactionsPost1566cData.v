Require Import isla.riscv64.riscv64.
From IslaTraces.write_success_blocks Require Import Index.
Require Import ZesuSsz.Contracts.IslarisCode.
Require Import ZesuSsz.Contracts.IslarisMachine.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessTransactionsLoopExitEvents.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessTransactionsPost15668DataStates.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessTransactionsPost1566c.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessTransactionsPuncturedScratch.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessTransactionsSpec.
Require Import IslaTraces.write_success_87.a1566c_spec.

Local Remove Hints subsume_instr_pre'_inst : typeclass_instances.
Local Existing Instance subsume_instr_pre_wand_inst | 1.

Lemma write_success_transactions_post_1566c_data
    `{!islaG Sigma} `{!threadG} (P : iProp Sigma) :
  instr_lookup_resources IslaTraces.write_success_blocks.Index.lookup -∗
  instr_body 0x15670 (writeSuccessTransactionsPost15670DataSpec P) -∗
  instr_body 0x1566c (writeSuccessTransactionsPost1566cDataSpec P).
Proof.
  iStartProof. iIntros "#Hlookup Hnext".
  iPoseProof "Hlookup" as "#Hlookup1566c".
  iEval (rewrite /instr_lookup_resources) in "Hlookup1566c".
  iPoseProof ("Hlookup1566c" $! 0x1566c with "[]") as "#Hinstr1566c".
  { iPureIntro. rewrite IslaTraces.write_success_blocks.Index.lookup_a1566c. done. }
  iPoseProof (IslaTraces.write_success_87.a1566c_spec.a1566c_spec
    0x1566c with "Hinstr1566c") as "Hld".
  rewrite instr_pre'_eq. iIntros "Hentry".
  iEval (rewrite /writeSuccessTransactionsPost1566cDataSpec) in "Hentry".
  iDestruct "Hentry" as
    (sp pointer base transactions bytes tail remaining first second items)
    "(Hsys & Hother & H2 & H10 & H11 & Harray & Hown & Hscratch &
      Hcarrier & Hwithdrawals & Hmmio & Htrace & %Halign16 & %Halign8 &
      %Hlow & %Hhigh & HP & _)".
  iDestruct (reg_col_lookup writeSuccessTransactionsOtherRegShapes 0%nat
    (KindReg "x1", BitsShape 64) with "Hother") as
    (ra Hra) "(Hx1 & Hother)".
  { vm_compute. reflexivity. }
  apply valu_has_bits_shape in Hra as (raBits & ->).
  iEval (rewrite /writeSuccessTransactionsLoopCarrierPayload
    /writeSuccessTransactionsWordsCarrier) in "Hcarrier".
  iDestruct "Hcarrier" as
    "((Hfirst & Hsecond & Hpointer & Hremaining) & HcallStack & Hitems & %Hfacts)".
  destruct Hfacts as
    (HsecondLength & HitemsLength & HfirstAlign & HfirstLower & HfirstUpper &
     HspExtract & HspCallLower & HspMax).
  pose proof HspExtract as HspExtractOriginal.
  bv_simplify HspExtract.
  iAssert ("x11" ↦ᵣ: fun _ => True)%I with "[H11]" as "H11Any".
  { rewrite reg_mapsto_pred_eq /reg_mapsto_pred_def. iExists _. iFrame. }
  rewrite /InstrSpecs.Specs.zesu_ld_spec /InstrSpecs.Specs.rv64_ld_spec.
  iApply "Hld". iExists second, sp. iFrame "Hsys H11Any H2 Hsecond".
  repeat iSplit; try iPureIntro; try assumption; try bv_solve; try lia.
  rewrite instr_pre'_eq. iNext. iIntros "Hpost".
  iApply "Hnext".
  iEval (rewrite /writeSuccessTransactionsPost15670DataSpec).
  iExists sp, pointer, base, transactions, bytes, tail, remaining, first, second,
    raBits, items.
  iDestruct "Hpost" as "(HsysPost & H11Post & H2Post & HsecondPost & _)".
  iFrame "HsysPost Hx1 Hother H2Post H10 H11Post Harray Hown Hscratch
    Hwithdrawals Hmmio Htrace HP".
  rewrite /writeSuccessTransactionsLoopCarrierPayload
    /writeSuccessTransactionsWordsCarrier.
  iFrame "Hfirst HsecondPost Hpointer Hremaining HcallStack Hitems".
  iSplit.
  { iPureIntro. repeat split; assumption. }
  repeat iSplit; try iPureIntro; try assumption; try done.
Qed.
