From Coq Require Import Lists.List ZArith.ZArith.
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Experiments.WriteSuccessNativeCalleeProviders.
Require Import ZesuSsz.Experiments.WriteSuccessNativeCode.
Require Import ZesuSsz.Experiments.WriteSuccessNativeTransactionLoopProvider.
Require Import ZesuSsz.Experiments.WriteSuccessHeaderSpec.
Require Import ZesuSsz.Experiments.WriteSuccessLoadHeaderPre.
Require Import ZesuSsz.Experiments.WriteSuccessToLoadWithFrame.
Require Import ZesuSsz.Experiments.WriteSuccessTransactionsSpec.
Require Import ZesuSsz.Experiments.WriteSuccessValueBlock.
Require Import ZesuSsz.Experiments.WriteSuccessValueTransactionsEntry.

Lemma write_success_native_load_header_with_frame_pre
    `{!islaG Sigma} `{!threadG} (P : iProp Sigma)
    (sp : bv 64) (sourceBytes : list (bv 8))
    (values : list (bv 64)) (payload : list (bv 8))
    (tail : spec) (base : Z) (transactions : list writeSuccessTransaction)
    (transactionBytes : list (bv 8)) :
  writeSuccessCompleteNativeCode -∗
  □ instr_pre 0x14d80
    (writeSuccessAtLoadHeaderWithFrame sp sourceBytes
      (writeSuccessHeaderEvents sp
        (writeSuccessValueEvents sp values
          (writeSuccessTransactionsEvents sp transactions tail)))
      (writeSuccessLoadHeaderRemainder P sp sourceBytes values payload tail base
        transactions transactionBytes)).
Proof.
  iStartProof. iIntros "#Hnative".
  iPoseProof (write_success_native_callee_providers with "Hnative")
    as "#Hcallees".
  iEval (rewrite /writeSuccessNativeCalleeProviders) in "Hcallees".
  iDestruct "Hcallees" as
    "(#Houtput & #Hmemcpy & #Hboolean & #Hoptional & #HbyteLists &
      #Hbytes & #Hu256 & #Hint1645 & #Hint & _)".
  iPoseProof (write_success_native_transaction_loop_provider
    (writeSuccessValueTransactionsContinuation values payload P)
    with "Hnative") as "#Hloop".
  iPoseProof (write_success_native_main_code with "Hnative") as "#Hmain".
  iEval (rewrite /writeSuccessNativeMainCode) in "Hmain".
  iDestruct "Hmain" as "(#Hlookup & #Hcode & _)".
  iApply (write_success_load_header_pre P sp sourceBytes values payload tail
    base transactions transactionBytes with
    "Hlookup Hcode Hmemcpy Houtput Hbytes Hint Hloop").
Qed.
