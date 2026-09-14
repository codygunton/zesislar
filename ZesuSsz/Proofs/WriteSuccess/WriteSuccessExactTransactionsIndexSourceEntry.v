Require Import ZesuSsz.Automation.All.
Require Import ZesuSsz.Automation.Resources.
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Export.Snapshots.
From ZesuSsz.Proofs.WriteSuccess Require Import
  WriteSuccessExactTransactionsIndexCell WriteSuccessTransactionsSpec
  WriteSuccessExactTransactionsSourceLayout WriteSuccessExactTransactionsGasLoads
  WriteSuccessExactTransactionsIndexFacts
  WriteSuccessExactTransactionsGasSignatureEntry WriteSuccessExactTransactionsSignatureFieldEntry
  WriteSuccessExactTransactionsOptionSourcesRegion WriteSuccessExactTransactionsFirstRecipientEntry
  WriteSuccessExactTransactionsRecipientPairTagEntry WriteSuccessExactTransactionsRecipientLowerPairsValueEntry
  WriteSuccessExactTransactionsValueMiddleWordsEntry WriteSuccessExactTransactionsRecipientWordsSignatureValuesEntry
  WriteSuccessExactTransactionsWideSignatureSuffixEntry WriteSuccessExactTransactionsNestedSourceEntry
  WriteSuccessExactTransactionsPrepareSourceEntry WriteSuccessExactTransactionsTypeSourceEntry.

Definition transactionIndexSourceData `{!islaG Sigma}
    (sp : bv 64) (base : Z) (bytes : list (bv 8)) (processed : nat)
    (tail : spec) (P : iProp Sigma) : iProp Sigma :=
  (base ↦ₘ∗ bytes ∗ mmio_range 0x2401a0c0 16 ∗
   spec_trace (writeOutputEvents (sp + BV 64 1744)%bv (BV 64 1)
     [default (BV 8 0) (bytes !! (288 * processed + 264)%nat)] tail) ∗
   ⌜base `mod` 8 = 0⌝ ∗ ⌜0x20000000 <= base⌝ ∗
   ⌜base + Z.of_nat (length bytes) < 0x40000000⌝ ∗
   ⌜(288 * processed + 288 <= length bytes)%nat⌝ ∗ P ∗ True)%I.
Global Instance : LithiumUnfold (@transactionIndexSourceData) := I.

Definition transactionIndexSourceCaller `{!islaG Sigma} `{!threadG}
    (sp : bv 64) (base : Z) (bytes : list (bv 8)) (processed : nat)
    (tail : spec) (P : iProp Sigma) : iProp Sigma :=
  (reg_col writeSuccessTransactionsOtherRegShapes ∗
   (bv_unsigned sp + 120) ↦ₘ? 128 ∗ (bv_unsigned sp + 256) ↦ₘ? 24 ∗
   (bv_unsigned sp + 1640) ↦ₘ? 256 ∗
   transactionIndexSourceData sp base bytes processed tail P ∗
   ⌜bv_unsigned sp + 1896 < 0x40000000⌝ ∗ True)%I.
Global Instance : LithiumUnfold (@transactionIndexSourceCaller) := I.

Lemma transactions_index_to_source `{!islaG Sigma} `{!threadG}
    sp base bytes processed tail (P : iProp Sigma) :
  transactionIndexCellPost sp (Z_to_bv 64 base) (Z_to_bv 64 (Z.of_nat processed))
    (transactionIndexSourceCaller sp base bytes processed tail P) -∗
  ∃ oldra : bv 64,
    transactionFirstSourceEntry sp
      (Z_to_bv 64 base + Z_to_bv 64 (Z.of_nat processed) * BV 64 288)%bv
      oldra base bytes (288 * processed) tail (transactionSourceRetainedStack sp base processed ∗ P ∗ True)%I.
Proof.
  iStartProof. iIntros "Hpost".
  iEval (unfold transactionIndexCellPost) in "Hpost".
  iDestruct "Hpost" as "(Hsys & Hsp & Hrow & H11 & HbaseWord & Hindex & %Halign & %Hlow & %HcellHigh & Hcaller & _)".
  iEval (unfold transactionIndexSourceCaller) in "Hcaller".
  iDestruct "Hcaller" as "(Hregs & Hlower & Hupper & HsourceScratch & Hdata & %Hhigh & _)".
  iEval (unfold transactionIndexSourceData) in "Hdata".
  iDestruct "Hdata" as "(Hbytes & Hmmio & Htrace & %HbaseAlign & %Hbase & %Hend & %Hbound & HP & _)".
  iDestruct (reg_col_lookup writeSuccessTransactionsOtherRegShapes 0 (KindReg "x1", BitsShape 64)
    ltac:(vm_compute; reflexivity) with "Hregs") as (v1 Hv1) "(Hra & Hregs)".
  destruct (valu_has_bits_shape _ _ Hv1) as [oldra ->].
  pose proof (transactions_index_cursor base bytes processed Hbase Hend Hbound HbaseAlign) as [Hcursor HrowAlign].
  iExists oldra. unfold transactionFirstSourceEntry.
  iAssert (∃ _ : unit, transactionFirstSourceEntry sp
    (Z_to_bv 64 base + Z_to_bv 64 (Z.of_nat processed) * BV 64 288)%bv oldra base bytes
    (288 * processed) tail (transactionSourceRetainedStack sp base processed ∗ P ∗ True)%I ∗ True)%I
    with "[Hsys Hregs Hsp Hrow H11 HbaseWord Hlower Hindex Hupper HsourceScratch Hbytes Hmmio Htrace Hra HP]" as "Hentry".
  { zesu_run. }
  iDestruct "Hentry" as (_) "[Hentry _]". iExact "Hentry".
Qed.
Print Assumptions transactions_index_to_source.
