Require Import ZesuSsz.Automation.All.
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Export.Snapshots.
From ZesuSsz.Proofs.WriteSuccess Require Import
  WriteSuccessExactTransactionsGasRecipientSource WriteSuccessExactTransactionsPriorityGasRegion
  WriteSuccessExactEncoderU128 WriteSuccessObservation WriteSuccessOutputSemantic.

Definition transactionNoncePricePriorityOutputTrace
    (sp nonce gaslow gashigh tag low high value : bv 64) tail : spec :=
  writeOutputEvents (sp - BV 64 16)%bv (BV 64 8)
    (writeSuccessPrivateBytes (writeSuccessEncodeU64 (bv_unsigned nonce)))
    (writeOutputEvents (sp - BV 64 32)%bv (BV 64 16)
      (writeSuccessU128WordsPayload gaslow gashigh)
      (transactionPriorityGasTrace sp tag low high value tail)).

Definition transactionChainPriceRecipientCaller `{!islaG Sigma} `{!threadG}
    (sp gaslow gashigh feeTag feeLow feeHigh value tag first second w0 w1 w2 w3
      old12 old13 data size count : bv 64) (last : bv 32) (bytes : list (bv 8)) (P : iProp Sigma) : iProp Sigma :=
  ("x24" ↦ᵣ RVal_Bits gashigh ∗ "x25" ↦ᵣ RVal_Bits gaslow ∗
   "x27" ↦ᵣ RVal_Bits feeTag ∗ "x9" ↦ᵣ RVal_Bits feeLow ∗ "x23" ↦ᵣ RVal_Bits feeHigh ∗
   "x26" ↦ᵣ RVal_Bits value ∗
   transactionGasRecipientSourceCore sp tag first second w0 w1 w2 w3 old12 old13
     data size count last bytes P ∗ True)%I.
Global Instance : LithiumUnfold (@transactionChainPriceRecipientCaller) := I.
