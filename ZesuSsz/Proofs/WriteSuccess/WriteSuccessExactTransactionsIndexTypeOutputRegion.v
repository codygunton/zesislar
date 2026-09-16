Require Import ZesuSsz.Automation.AllLegacy.
Require Import ZesuSsz.Automation.Continuations.
Require Import ZesuSsz.Automation.CodeLookup.
Require Import isla.riscv64.riscv64.
From ZesuSsz.Proofs.WriteSuccess Require Import
  WriteSuccessNativeCode WriteSuccessExactTransactionsIndexCell
  WriteSuccessExactTransactionsIndexSourceEntry WriteSuccessExactTransactionsSourceLayout
  WriteSuccessExactTransactionsFirstTypeOutputRegion WriteSuccessExactTransactionsTypeSourceEntry
  WriteSuccessExactTransactionsTypeOutput WriteSuccessExactTransactionsGasLoads.

Lemma transactions_index_type_output_region_correct `{!islaG Sigma} `{!threadG}
    (sp : bv 64) (base : Z) (bytes : list (bv 8)) (processed : nat)
    (olddata : bv 64) (tail : spec) (P : iProp Sigma) :
  writeSuccessCompleteNativeCode -∗
  instr_body 0x150f0 (transactionTypeOutputPost (sp + BV 64 1744)%bv
    (default (BV 8 0) (bytes !! (288 * processed + 264)%nat)) tail
    (transactionTypeSourceRetained sp
      (Z_to_bv 64 base + Z_to_bv 64 (Z.of_nat processed) * BV 64 288)%bv
      (transactionRowWord bytes (288 * processed) 160)
      (transactionRowWord bytes (288 * processed) 168) base bytes (288 * processed)
      (transactionSourceRetainedStack sp base processed ∗ P ∗ True)%I)) -∗
  instr_body 0x14f08 (transactionIndexCellEntry sp (Z_to_bv 64 base)
    (Z_to_bv 64 (Z.of_nat processed)) olddata
    (transactionIndexSourceCaller sp base bytes processed tail P)).
Proof.
  iStartProof. iIntros "#Hcode Hnext".
  iPoseProof "Hcode" as "Hbundle".
  iEval (rewrite /writeSuccessCompleteNativeCode) in "Hbundle".
  iDestruct "Hbundle" as
    "#(Hprologue & Hlookup & Hmain & Houtput & Hmemcpy & Hboolean & Hoptional & HbyteLists & Hbytes & Hint & Hu256 & Hu128)".
  iAssert ([∗ list] instruction ∈ take 5 IslaTraces.write_success_29.instrs.instr_map,
    instr instruction.1 (Some instruction.2))%I as "#Hindex".
  { iApply instr_lookup_collect; last iExact "Hlookup". repeat constructor; reflexivity. }
  iApply (transactions_index_cell_correct with "Hindex").
  iAssert (instr_body 0x14f1c (∃ oldra : bv 64, transactionFirstSourceEntry sp
    (Z_to_bv 64 base + Z_to_bv 64 (Z.of_nat processed) * BV 64 288)%bv
    oldra base bytes (288 * processed) tail
    (transactionSourceRetainedStack sp base processed ∗ P ∗ True)%I)) with "[Hnext]" as "Hsource".
  { iApply instr_body_exists. iIntros (oldra).
    unfold transactionFirstSourceEntry.
    iApply (transactions_first_type_output_region_correct with "Hcode Hnext"). }
  iApply (instr_pre_wand 0x14f1c 0x14f1c false false with "Hsource"); [done | done |].
  iIntros "Hpost". iApply transactions_index_to_source. iExact "Hpost".
Qed.
Print Assumptions transactions_index_type_output_region_correct.
