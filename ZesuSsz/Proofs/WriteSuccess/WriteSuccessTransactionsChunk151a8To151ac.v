Require Import ZesuSsz.Automation.All.
From Coq Require Import Lists.List ZArith.ZArith.
Require Import isla.riscv64.riscv64.
From IslaTraces.write_success_blocks Require Import Index.
Require Import ZesuSsz.Contracts.IslarisCode.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessTransactionsBoundary1519c.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessTransactionsBoundary151a8.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessTransactionsChunk151a8MoveSpec.

Local Existing Instance subsume_instr_pre_wand_inst | 1.

Lemma write_success_transactions_chunk_151a8_to_151ac
    `{!islaG Sigma} `{!threadG} (P : iProp Sigma) :
  instr_lookup_resources IslaTraces.write_success_blocks.Index.lookup -∗
  IslaTraces.write_success_blocks.Index.spec_instr_resources -∗
  instr_body 0x151ac (writeSuccessTransactionsAt151acSpec P) -∗
  instr_body 0x151a8 (writeSuccessTransactionsAt151a8Spec P).
Proof.
  iIntros "#Hlookup _ Hnext".
  rewrite instr_pre'_eq. iIntros "Hentry".
  iEval (rewrite /writeSuccessTransactionsAt151a8Spec) in "Hentry".
  iDestruct "Hentry" as
    (sp base transaction transactions processed remaining bytes prefix suffix tail)
    "(%Halign & %Hmin & %Hmax & Hphase)".
  iDestruct "Hphase" as
    "(Hmachine & HbasePrefix & HbaseSuffix & Hprocessed & Htransaction &
      Hremaining & Hmmio & Htrace & HP & Hinvariant & Hexit & _)".
  iEval (rewrite /writeSuccessTransactionsMachine151a8) in "Hmachine".
  iDestruct "Hmachine" as
    "(Hsys & Hother & H2 & H5 & H8 & H9 & H10 & H11 & H12 & H18 & H19 &
      H20 & H21 & H22 & H23 & H24 & H25 & H26 & H27 & Hscratch & _)".
  iEval (rewrite !reg_col_cons reg_col_nil) in "Hother".
  iDestruct "Hother" as
    "(H1 & H3 & H4 & H6 & H7 & H13 & H14 & H15 & H16 & H17 & H28 & H29 &
      H30 & H31)".
  iDestruct "H13" as (oldX13) "(%H13shape & H13map)".
  iAssert (("x13" ↦ᵣ: fun _ => True))%I with "[H13map]" as "H13any".
  { rewrite reg_mapsto_pred_eq /reg_mapsto_pred_def.
    iExists oldX13. iSplit; first iExact "H13map". done. }
  iEval (rewrite /instr_lookup_resources) in "Hlookup".
  iPoseProof ("Hlookup" $! 0x151a8 with "[]") as "#Hinstr151a8".
  { iPureIntro. rewrite IslaTraces.write_success_blocks.Index.lookup_a151a8.
    done. }
  iPoseProof (write_success_transactions_151a8_move_spec 0x151a8
    with "Hinstr151a8") as "Hmove".
  iEval (rewrite instr_pre'_eq) in "Hmove".
  iApply "Hmove".
  iExists (WriteSuccessTransactionsSpec.writeSuccessTransactionWord transaction 72).
  iSplitL "Hsys"; first iExact "Hsys".
  iSplitL "H13any"; first iExact "H13any".
  iFrame "H21".
  iEval (rewrite -instr_pre'_eq) in "Hnext".
  iApply (instr_pre_wand with "Hnext"); first done; first reflexivity.
  iIntros "Hpost".
  iDestruct "Hpost" as "(Hsys & H13 & H21 & _)".
  iAssert (("x12" ↦ᵣ: fun value =>
    ⌜valu_has_shape value (BitsShape 64)⌝))%I with "[H12]" as "H12raw".
  { rewrite reg_mapsto_pred_eq /reg_mapsto_pred_def.
    iExists _. iSplit; first iExact "H12". done. }
  iAssert (("x13" ↦ᵣ: fun value =>
    ⌜valu_has_shape value (BitsShape 64)⌝))%I with "[H13]" as "H13raw".
  { rewrite reg_mapsto_pred_eq /reg_mapsto_pred_def.
    iExists _. iSplit; first iExact "H13". done. }
  iEval (rewrite reg_mapsto_pred_eq /reg_mapsto_pred_def) in "H12raw H13raw".
  iDestruct "H12raw" as (x12) "(H12map & %H12shape)".
  iDestruct "H13raw" as (x13) "(H13map & %H13postshape)".
  iAssert ((∃ value : valu, ⌜valu_has_shape value (BitsShape 64)⌝ ∗
    KindReg "x12" ↦ᵣₖ value)%I) with "[H12map]" as "H12pred".
  { iExists x12. iSplit; [iPureIntro; exact H12shape | iExact "H12map"]. }
  iAssert ((∃ value : valu, ⌜valu_has_shape value (BitsShape 64)⌝ ∗
    KindReg "x13" ↦ᵣₖ value)%I) with "[H13map]" as "H13pred".
  { iExists x13.
    iSplit; [iPureIntro; exact H13postshape | iExact "H13map"]. }
  iAssert (reg_col
    ((fun register => (KindReg register, BitsShape 64)) <$>
      ["x1"; "x3"; "x4"; "x6"; "x7"; "x12"; "x13"; "x14"; "x15";
       "x16"; "x17"; "x28"; "x29"; "x30"; "x31"]))%I
    with "[H1 H3 H4 H6 H7 H12pred H13pred H14 H15 H16 H17 H28 H29 H30 H31]"
    as "Hother151ac".
  { iEval (rewrite !reg_col_cons reg_col_nil).
    iFrame "H1 H3 H4 H6 H7 H12pred H13pred H14 H15 H16 H17 H28 H29 H30 H31". }
  iAssert (writeSuccessTransactionsMachine151ac
    sp base transactions processed transaction)%I
    with "[Hsys Hother151ac H2 H5 H8 H9 H10 H11 H18 H19 H20 H21 H22 H23 H24
      H25 H26 H27 Hscratch]" as "Hmachine151ac".
  { rewrite /writeSuccessTransactionsMachine151ac.
    iFrame "Hsys Hother151ac H2 H5 H8 H9 H10 H11 H18 H19 H20 H21 H22 H23 H24
      H25 H26 H27 Hscratch". }
  rewrite /writeSuccessTransactionsAt151acSpec.
  iExists sp, base, transaction, transactions, processed, remaining,
    bytes, prefix, suffix, tail.
  iSplit; first by iPureIntro.
  iSplit; first by iPureIntro.
  iSplit; first by iPureIntro.
  rewrite /WriteSuccessTransactionsSpec.writeSuccessTransactionPhaseHandoff.
  iFrame "Hmachine151ac HbasePrefix HbaseSuffix Hprocessed Htransaction
    Hremaining Hmmio Htrace HP Hinvariant Hexit".
Qed.
