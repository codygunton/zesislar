Require Import ZesuSsz.Automation.All.
From Coq Require Import Lists.List.
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessTransactionsSpec.

Definition writeSuccessTransactions10190SavedHead
    (transaction : writeSuccessTransaction) : list (reg_kind * valu_shape) :=
  [(KindReg "x8",
    ExactShape (RVal_Bits (writeSuccessTransactionWord transaction 192)));
   (KindReg "x9",
    ExactShape (RVal_Bits (writeSuccessTransactionWord transaction 16)));
   (KindReg "x18",
    ExactShape (RVal_Bits (writeSuccessTransactionWord transaction 48)))].

Definition writeSuccessTransactions10190SavedMiddle
    (transaction : writeSuccessTransaction) : list (reg_kind * valu_shape) :=
  [(KindReg "x19",
    ExactShape (RVal_Bits (writeSuccessTransactionWord transaction 224)));
   (KindReg "x20",
    ExactShape (RVal_Bits (writeSuccessTransactionWord transaction 56)));
   (KindReg "x21",
    ExactShape (RVal_Bits (writeSuccessTransactionWord transaction 72)))].

Definition writeSuccessTransactions10190SavedTail
    (transaction : writeSuccessTransaction) : list (reg_kind * valu_shape) :=
  [(KindReg "x22",
    ExactShape (RVal_Bits (writeSuccessTransactionWord transaction 200)));
   (KindReg "x23",
    ExactShape (RVal_Bits (writeSuccessTransactionWord transaction 24)));
   (KindReg "x24",
    ExactShape (RVal_Bits (writeSuccessTransactionWord transaction 8)));
   (KindReg "x25",
    ExactShape (RVal_Bits (writeSuccessTransactionWord transaction 0)));
   (KindReg "x26",
    ExactShape (RVal_Bits (writeSuccessTransactionWord transaction 184)));
   (KindReg "x27",
    ExactShape
      (RVal_Bits
        (bv_zero_extend 64 (writeSuccessTransactionByte transaction 32))))].

Definition writeSuccessTransactions10190SavedAll
    (transaction : writeSuccessTransaction) : list (reg_kind * valu_shape) :=
  writeSuccessTransactions10190SavedHead transaction ++
  writeSuccessTransactions10190SavedMiddle transaction ++
  writeSuccessTransactions10190SavedTail transaction.
