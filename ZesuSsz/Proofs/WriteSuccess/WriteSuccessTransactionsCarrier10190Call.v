From Coq Require Import Lists.List ZArith.ZArith.
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Contracts.IslarisCode.
Require Import ZesuSsz.Contracts.IslarisMachine.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessCallAbi.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessCalls.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessByteLists.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessEvents.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessTransactionsSpec.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessTransactionsBoundary150f0.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessTransactionsCarrierCall150ec.

Import ListNotations.

Local Remove Hints subsume_instr_pre'_inst : typeclass_instances.
Local Existing Instance subsume_instr_pre_wand_inst | 1.

Lemma write_success_transactions_carrier_150ec_call_frame_facts
    `{!islaG Sigma} `{!threadG} (P : iProp Sigma)
    (sp : bv 64) (base : Z) (transaction : writeSuccessTransaction)
    (transactions processed remaining : list writeSuccessTransaction)
    (bytes prefix suffix : list (bv 8)) (tail : spec)
    (first second third fourth : bv 64) (items : list ByteListItem) :
  writeSuccessTransactions150ecCarrierCallFrame P sp base transaction
    transactions processed remaining bytes prefix suffix tail
    first second third fourth items -∗
  writeSuccessTransactions150ecCarrierCallFrame P sp base transaction
      transactions processed remaining bytes prefix suffix tail
      first second third fourth items ∗
    ⌜bv_unsigned sp `mod` 16 = 0⌝ ∗
    ⌜0x20000000 <= bv_unsigned sp⌝ ∗
    ⌜bv_unsigned sp < 0x40000000⌝.
Proof.
  iIntros "Hframe".
  iEval (unfold writeSuccessTransactions150ecCarrierCallFrame) in "Hframe".
  iDestruct "Hframe" as
    "(H34 & Hscratch & Harray & Hprefix & Hsuffix & Hprocessed & Hdata &
      Hrest & Hremaining & HP & Hinvariant & Hexit & HloadFacts & _)".
  iDestruct "Hinvariant" as "#Hinvariant".
  iPoseProof "Hinvariant" as "Hfacts".
  iEval (unfold writeSuccessTransactionsInvariant) in "Hfacts".
  iDestruct "Hfacts" as
    "(_ & _ & _ & _ & _ & _ & _ & _ & _ & %HspAlign & %HspMin &
      %HspMax & _)".
  iSplitL "H34 Hscratch Harray Hprefix Hsuffix Hprocessed Hdata Hrest
    Hremaining HP Hexit HloadFacts".
  - rewrite /writeSuccessTransactions150ecCarrierCallFrame. iFrame. done.
  - repeat iSplit; iPureIntro; try assumption; lia.
Qed.

Lemma write_success_transactions_carrier_10190_return
    `{!islaG Sigma} `{!threadG} (P : iProp Sigma)
    (sp : bv 64) (base : Z) (transaction : writeSuccessTransaction)
    (transactions processed remaining : list writeSuccessTransaction)
    (bytes prefix suffix : list (bv 8)) (tail : spec)
    (first second third fourth : bv 64) (items : list ByteListItem) :
  instr_body 0x150f0 (writeSuccessTransactionsAt150f0CarrierCallSpec P) -∗
  instr_pre 0x150f0
    (zesu_c_call_ret 0
      (writeSuccessTransactions150ecSavedValues transaction)
      (BV 64 0x150f0) sp
      (fun _ =>
        writeSuccessTransactions150ecCarrierCallFrame P sp base transaction
          transactions processed remaining bytes prefix suffix tail
          first second third fourth items ∗
        mmio_range 0x2401a0c0 16 ∗
        spec_trace
          (writeSuccessTransactionPhaseEvents TransactionChainId sp transaction
            (writeSuccessTransactionsEvents sp remaining
              (writeSuccessTransactionsCarrierOutputTail sp items tail))) ∗
        True)).
Proof.
  iIntros "Hnext".
  iApply instr_pre_to_body. iNext.
  iApply (instr_pre_wand 0x150f0 0x150f0 false false with "Hnext");
    [done | done |].
  rewrite /zesu_c_call_ret.
  iIntros "(Hsys & Hcaller & Hsaved & Hrest)".
  iEval (rewrite reg_mapsto_pred_eq /reg_mapsto_pred_def) in "Hrest".
  iDestruct "Hrest" as (r10) "(H10 & Hrest)".
  iDestruct "Hrest" as (b10) "(%Hr10 & Hrest)".
  iDestruct "Hrest" as (r11) "(H11 & Hrest)".
  iDestruct "Hrest" as (b11) "(%Hr11 & H2 & Hzero & Hpost)".
  iDestruct "Hpost" as "(Hframe & Hmmio & Htrace & _)".
  rewrite /writeSuccessTransactionsAt150f0CarrierCallSpec.
  iExists sp, base, transaction, transactions, processed, remaining,
    bytes, prefix, suffix, tail, first, second, third, fourth, items.
  rewrite /writeSuccessTransactionsMachine150f0CarrierCall
    /writeSuccessTransactions150ecSavedValues
    /tmp_registers !reg_col_cons reg_col_nil.
  cbn. subst r10 r11.
  iFrame.
  repeat iSplit; iPureIntro; cbn; done.
  all: try (rewrite mem_mapsto_uninit_0; iPureIntro; bv_solve).
Qed.

Lemma write_success_transactions_carrier_10190_call
    `{!islaG Sigma} `{!threadG} (P : iProp Sigma) :
  □ instr_pre 0x10190 zesuWriteOutputCallSpec -∗
  instr_body 0x150f0 (writeSuccessTransactionsAt150f0CarrierCallSpec P) -∗
  instr_pre 0x10190 (writeSuccessTransactionsAt10190CarrierCallSpec P).
Proof.
  iIntros "#Houtput Hnext".
  iApply (instr_pre_wand 0x10190 0x10190 true true with "Houtput");
    [done | done |].
  rewrite /writeSuccessTransactionsAt10190CarrierCallSpec.
  iIntros "Hentry".
  iDestruct "Hentry" as
    (sp base transaction transactions processed remaining bytes prefix suffix
      tail first second third fourth items)
    "(Hsys & Hcaller & Hsaved & H10 & H11 & H1 & H2 & Hmmio & Htrace &
      Hframe & _)".
  iPoseProof (write_success_transactions_carrier_150ec_call_frame_facts P sp
    base transaction transactions processed remaining bytes prefix suffix tail
    first second third fourth items with "Hframe") as
    "(Hframe & %HspAlign & %HspMin & %HspMax)".
  iPoseProof (write_success_transactions_carrier_10190_return P sp base
    transaction transactions processed remaining bytes prefix suffix tail
    first second third fourth items with "Hnext") as "HreturnWithFrame".
  iPoseProof (zesu_c_call_ret_frame 0
    (writeSuccessTransactions150ecSavedValues transaction) (BV 64 0x150f0) sp
    (writeSuccessTransactions150ecCarrierCallFrame P sp base transaction
      transactions processed remaining bytes prefix suffix tail
      first second third fourth items)
    (fun _ =>
      mmio_range 0x2401a0c0 16 ∗
      spec_trace
        (writeSuccessTransactionPhaseEvents TransactionChainId sp transaction
          (writeSuccessTransactionsEvents sp remaining
            (writeSuccessTransactionsCarrierOutputTail sp items tail))) ∗ True)%I
    with "HreturnWithFrame Hframe") as "Hreturn".
  iEval (rewrite /writeSuccessTransactions150ecCallerRegisters
    /writeSuccessTransactions150ecCallerValues
    /writeSuccessTransactions150ecSavedValues
    !reg_col_cons reg_col_nil) in "Hcaller Hsaved".
  iDestruct "Hcaller" as
    "(H5 & H6 & H7 & H12 & H13 & H14 & H15 & H16 & H17 & H28 & H29 &
      H30 & H31 & _)".
  iDestruct "Hsaved" as
    "(H8 & H9 & H18 & H19 & H20 & H21 & H22 & H23 & H24 & H25 & H26 &
      H27 & _)".
  iDestruct "H5" as (v5) "(%Hv5 & H5)"; cbn in Hv5; subst v5.
  iDestruct "H6" as (v6) "(%Hv6 & H6)"; cbn in Hv6; subst v6.
  iDestruct "H7" as (v7) "(%Hv7 & H7)"; cbn in Hv7; subst v7.
  iDestruct "H12" as (v12) "(%Hv12 & H12)"; cbn in Hv12; subst v12.
  iDestruct "H13" as (v13) "(%Hv13 & H13)"; cbn in Hv13; subst v13.
  iDestruct "H14" as (v14) "(%Hv14 & H14)"; cbn in Hv14; subst v14.
  iDestruct "H15" as (v15) "(%Hv15 & H15)"; cbn in Hv15; subst v15.
  iDestruct "H16" as (v16) "(%Hv16 & H16)"; cbn in Hv16; subst v16.
  iDestruct "H17" as (v17) "(%Hv17 & H17)"; cbn in Hv17; subst v17.
  iDestruct "H28" as (v28) "(%Hv28 & H28)"; cbn in Hv28; subst v28.
  iDestruct "H29" as (v29) "(%Hv29 & H29)"; cbn in Hv29; subst v29.
  iDestruct "H30" as (v30) "(%Hv30 & H30)"; cbn in Hv30; subst v30.
  iDestruct "H31" as (v31) "(%Hv31 & H31)"; cbn in Hv31; subst v31.
  iDestruct "H8" as (v8) "(%Hv8 & H8)"; cbn in Hv8; subst v8.
  iDestruct "H9" as (v9) "(%Hv9 & H9)"; cbn in Hv9; subst v9.
  iDestruct "H18" as (v18) "(%Hv18 & H18)"; cbn in Hv18; subst v18.
  iDestruct "H19" as (v19) "(%Hv19 & H19)"; cbn in Hv19; subst v19.
  iDestruct "H20" as (v20) "(%Hv20 & H20)"; cbn in Hv20; subst v20.
  iDestruct "H21" as (v21) "(%Hv21 & H21)"; cbn in Hv21; subst v21.
  iDestruct "H22" as (v22) "(%Hv22 & H22)"; cbn in Hv22; subst v22.
  iDestruct "H23" as (v23) "(%Hv23 & H23)"; cbn in Hv23; subst v23.
  iDestruct "H24" as (v24) "(%Hv24 & H24)"; cbn in Hv24; subst v24.
  iDestruct "H25" as (v25) "(%Hv25 & H25)"; cbn in Hv25; subst v25.
  iDestruct "H26" as (v26) "(%Hv26 & H26)"; cbn in Hv26; subst v26.
  iDestruct "H27" as (v27) "(%Hv27 & H27)"; cbn in Hv27; subst v27.
  rewrite /zesuWriteOutputCallSpec /zesu_c_call.
  iExists sp, (BV 64 0x150f0).
  cbn [tmp_registers reg_col].
  iEval (rewrite !reg_mapsto_pred_eq /reg_mapsto_pred_def).
  iFrame.
  repeat (iSplit; first (iPureIntro; cbn; done)).
  repeat iSplit; try iPureIntro; try assumption; try bv_solve; try lia;
    try iFrame.
  all: try (rewrite mem_mapsto_uninit_0; iPureIntro; bv_solve).
  all: cbn.
  all: try (do 6 (iExists _; iSplit; [iPureIntro; reflexivity |])).
  all: repeat (iSplit; first (iPureIntro; try reflexivity; try assumption;
    try bv_solve; try lia)).
  all: try (rewrite mem_mapsto_uninit_0; iPureIntro; bv_solve).
  all: try iEmpIntro.
  Unshelve. all: try reflexivity; exact inhabitant.
Qed.
