From Coq Require Import Lists.List ZArith.ZArith.
Require Import isla.riscv64.riscv64.
Require Import InstrSpecs.Specs.
Require Import IslaTraces.write_success_49.a151a4_spec.
Require Import ZesuSsz.Contracts.IslarisCode.
Require Import ZesuSsz.Experiments.WriteSuccessBitvector.
Require Import ZesuSsz.Experiments.WriteSuccessTransactionsChunk151a4LoadState.

Local Remove Hints a151a4_spec_inst : typeclass_instances.
Local Remove Hints subsume_instr_pre'_inst : typeclass_instances.
Local Existing Instance subsume_instr_pre_wand_inst | 1.

Lemma write_success_transactions_151a4_load_core
    `{!islaG Sigma} `{!threadG} (P : iProp Sigma)
    (sp : bv 64) (base : Z)
    (transaction : WriteSuccessTransactionsSpec.writeSuccessTransaction)
    (transactions processed remaining :
      list WriteSuccessTransactionsSpec.writeSuccessTransaction)
    (bytes prefix suffix : list (bv 8)) (tail : spec) :
  instr 0x151a4 (Some IslaTraces.write_success_49.a151a4.a151a4) -∗
  instr_body 0x151a8
    (writeSuccessTransactions151a4LoadResult P sp base transaction transactions
      processed remaining bytes prefix suffix tail) -∗
  instr_body 0x151a4
    (writeSuccessTransactions151a4LoadState P sp base transaction transactions
      processed remaining bytes prefix suffix tail).
Proof.
  iIntros "#Hinstr Hnext".
  iPoseProof (IslaTraces.write_success_49.a151a4_spec.a151a4_spec 0x151a4
    with "Hinstr") as "Hload".
  rewrite instr_pre'_eq. iIntros "Hstate".
  rewrite /writeSuccessTransactions151a4LoadState.
  iDestruct "Hstate" as
    "(Hsys & H12 & H2 & Hword & Hframe & Houter & %HspAlign & %HspMin & %HspMax & %Halign & %Hmin & %Hmax & _)".
  have Halign8 : bv_unsigned sp `mod` 8 = 0 by lia.
  iApply "Hload".
  rewrite /InstrSpecs.Specs.zesu_ld_spec.
  iExists (WriteSuccessTransactionsSpec.writeSuccessTransactionWord
    transaction 64), sp.
  iFrame "Hsys H12 H2 Hword".
  iSplit; first by iPureIntro; exact Halign8.
  iSplit; first by iPureIntro; lia.
  iEval (rewrite -instr_pre'_eq) in "Hnext".
  iApply (instr_pre_wand with "Hnext"); first done; first reflexivity.
  iIntros "Hpost".
  iDestruct "Hpost" as "(Hsys & H12 & H2 & Hword & _)".
  assert (Hsign : bv_sign_extend 64
    (WriteSuccessTransactionsSpec.writeSuccessTransactionWord transaction 64) =
    WriteSuccessTransactionsSpec.writeSuccessTransactionWord transaction 64)
    by apply bv_sign_extend_idemp.
  iAssert ("x12" ↦ᵣ RVal_Bits (bv_sign_extend 64
    (WriteSuccessTransactionsSpec.writeSuccessTransactionWord transaction 64)))%I
    with "[H12]" as "H12signed".
  { rewrite Hsign. iExact "H12". }
  iSpecialize ("Hframe" with "Hsys H12signed H2 Hword").
  rewrite /writeSuccessTransactions151a4LoadResult.
  iFrame.
  iSplit; first by iPureIntro.
  iSplit; first by iPureIntro.
  iSplit; first by iPureIntro.
  done.
Qed.
