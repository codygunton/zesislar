Require Import ZesuSsz.Automation.All.
Require Import isla.riscv64.riscv64.
From ZesuSsz.Proofs.WriteSuccess Require Import
  WriteSuccessExactTransactionsGasLoads WriteSuccessExactTransactionsGasSignatureEntry
  WriteSuccessExactTransactionsSignatureFieldEntry WriteSuccessExactTransactionsOptionSourcesRegion
  WriteSuccessExactTransactionsFirstRecipientEntry WriteSuccessExactTransactionsRecipientPairTagEntry
  WriteSuccessExactTransactionsRecipientLowerPairsValueEntry WriteSuccessExactTransactionsValueMiddleWordsEntry
  WriteSuccessExactTransactionsRecipientWordsSignatureValuesEntry WriteSuccessExactTransactionsWideSignatureSuffixEntry
  WriteSuccessExactTransactionsNestedSourceEntry WriteSuccessExactTransactionsPrepareSourceEntry
  WriteSuccessExactTransactionsTypeSourceEntry.

Definition transactionFirstSourceEntry `{!islaG Sigma} `{!threadG}
    (sp row oldra : bv 64) (base : Z) (bytes : list (bv 8)) (index : nat)
    (tail : spec) (P : iProp Sigma) : iProp Sigma :=
  transactionGasLoadEntry row base bytes index
    (transactionGasSignatureCaller sp bytes index
      (transactionSignatureFieldCaller sp bytes index
        (reg_col [(KindReg "x14", BitsShape 64); (KindReg "x15", BitsShape 64)] ∗
         (reg_col ((fun register => (KindReg register, BitsShape 64)) <$>
           ["x16"; "x17"; "x5"; "x6"; "x7"]) ∗
          transactionOptionValuesCaller (transactionRecipientSourceCaller sp (transactionToTagDestination sp (transactionValuePrefixCaller (transactionRecipientMiddlePairCaller sp (transactionSignatureValuesCaller sp
            (transactionSignatureSuffixCaller sp (transactionSignatureTailCaller sp
              (transactionNestedListsCaller sp (transactionNestedSuffixCaller sp (transactionPrepareCaller sp (transactionTypeSourceCaller sp oldra (default (BV 8 0) (bytes !! (index + 264)%nat)) tail P))))))))))) ∗ True) ∗ True)%I)).
Global Instance : LithiumUnfold (@transactionFirstSourceEntry) := I.

Definition transactionSourceRetainedStack `{!islaG Sigma} `{!threadG}
    (sp : bv 64) (base : Z) (processed : nat) : iProp Sigma :=
  ((bv_unsigned sp + 104) ↦ₘ Z_to_bv 64 base ∗
   (bv_unsigned sp + 248) ↦ₘ Z_to_bv 64 (Z.of_nat processed) ∗
   (bv_unsigned sp + 1660) ↦ₘ? 4 ∗
   (bv_unsigned sp + 1680) ↦ₘ? 64 ∗ (bv_unsigned sp + 1745) ↦ₘ? 151 ∗
   reg_col [(KindReg "x3", BitsShape 64); (KindReg "x4", BitsShape 64)] ∗ True)%I.
Global Instance : LithiumUnfold (@transactionSourceRetainedStack) := I.
