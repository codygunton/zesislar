Require Import ZesuSsz.Automation.AllLegacy.
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessBlobHashesLoop.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessNativeCalleeProviders.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessNativeCode.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessTransactionsAuthorizationsAnyLoop.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessTransactionsLoop.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessTransactionsSpec.

(** The closed transaction Loop contract derived from the complete code. *)
Lemma write_success_native_transaction_loop_provider
    `{!islaG Sigma} `{!threadG} (P : iProp Sigma) :
  writeSuccessCompleteNativeCode -∗
  □ instr_pre 0x14f04 (writeSuccessTransactionsLoopSpec P).
Proof.
  iStartProof.
  iIntros "#Hnative".
  iPoseProof (write_success_native_callee_providers with
    "Hnative") as "#Hcallees".
  rewrite /writeSuccessNativeCalleeProviders.
  iDestruct "Hcallees" as
    "(#Houtput & #Hmemcpy & #Hboolean & #Hoptional & #HbyteLists &
      #Hbytes & #Hu256 & #Hint1645 & #Hint & _)".
  rewrite /writeSuccessCompleteNativeCode.
  iDestruct "Hnative" as
    "(#Hprologue & #Hlookup & #Hmain & #HoutputCode & #HmemcpyCode &
      #HbooleanCode & #HoptionalCode & #HbyteListsCode & #HbytesCode &
      #HintCode & #Hu256Code & #Hint1645Code)".
  iPoseProof (write_success_blob_hashes_loop_pre P with
    "Hlookup Hmain Houtput") as "#HblobHashes".
  iPoseProof (write_success_transactions_authorizations_any_loop_pre P with
    "Hlookup Hmain Hmemcpy Hu256 Hint Houtput") as "#Hauthorizations".
  iApply (write_success_transactions_loop_pre P with
    "Hlookup Hmain Hmemcpy Houtput HblobHashes Hauthorizations Hboolean
      Hoptional Hbytes Hu256 Hint1645 Hint").
Qed.
