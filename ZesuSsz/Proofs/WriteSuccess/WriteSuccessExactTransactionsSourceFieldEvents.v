Require Import ZesuSsz.Automation.All.
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Export.Snapshots.
From ZesuSsz.Proofs.WriteSuccess Require Import
  WriteSuccessExactTransactionsSourceFieldLayout WriteSuccessExactTransactionsGasLoads
  WriteSuccessExactTransactionsFlagLoads WriteSuccessExactTransactionsChainPriceFrame
  WriteSuccessExactTransactionsRecipientBranchHandoff WriteSuccessExactTransactionsRecipientDataAccessRegion
  WriteSuccessExactAccessListsSpec WriteSuccessExactAccessListsReturnCount
  WriteSuccessExactAccessListsReturnLoopEntry WriteSuccessExactTransactionsDataAccessEntry
  WriteSuccessOutputSemantic WriteSuccessObservation WriteSuccessAccessListsSpec.

Definition transactionSourceAfterChainEvents (sp : bv 64) (bytes : list (bv 8)) (index : nat)
    (dataBytes : list (bv 8)) (entries : list writeSuccessAccessEntry) tail : spec :=
  transactionNoncePricePriorityOutputTrace sp (transactionRowWord bytes index 176)
    (transactionRowWord bytes index 0) (transactionRowWord bytes index 8)
    (transactionRowByte bytes index 32) (transactionRowWord bytes index 16)
    (transactionRowWord bytes index 24) (transactionRowWord bytes index 184)
    (transactionRecipientValueTrace sp (transactionRowByte bytes index 285)
      (transactionRecipientSourceWord bytes index 265) (transactionRecipientSourceWord bytes index 273)
      (transactionRowWord bytes index 48) (transactionRowWord bytes index 56)
      (transactionRowWord bytes index 64) (transactionRowWord bytes index 72)
      (transactionRecipientSourceLast bytes index)
      (transactionDataAccessOutputTrace (transactionRowWord bytes index 192)
        (transactionRowWord bytes index 200) sp (transactionRowWord bytes index 216) dataBytes
        (writeSuccessExactAccessListsEvents sp entries
          (writeOutputEvents (sp - BV 64 16)%bv (BV 64 8)
            (writeSuccessPrivateBytes (writeSuccessEncodeU64
              (bv_unsigned (transactionRowWord bytes index 232)))) tail)))).

Definition transactionSourceFieldPost `{!islaG Sigma} `{!threadG}
    (sp : bv 64) (base : Z) (bytes : list (bv 8)) (processed index : nat)
    (dataBytes accessBytes chainBytes : list (bv 8)) (entries : list writeSuccessAccessEntry)
    tail (Q : iProp Sigma) : iProp Sigma :=
  accessReturnCountPost sp (transactionRowWord bytes index 232) tail
    (accessReturnLoopFrame sp (bv_unsigned (transactionRowWord bytes index 208)) entries accessBytes
      (transactionRowWord bytes index 224)
      (transactionAccessRetainedMemory sp (transactionRowByte bytes index 285)
        (transactionRecipientSourceWord bytes index 265) (transactionRecipientSourceWord bytes index 273)
        (transactionRowWord bytes index 64) (transactionRowWord bytes index 192)
        (transactionRecipientSourceLast bytes index) dataBytes
        (bv_unsigned (sp + BV 64 1664)%bv ↦ₘ∗ chainBytes ∗
          transactionFieldSourceRetained sp base bytes processed index dataBytes accessBytes Q ∗ True)%I)).
Global Instance : LithiumUnfold (@transactionSourceFieldPost) := I.
