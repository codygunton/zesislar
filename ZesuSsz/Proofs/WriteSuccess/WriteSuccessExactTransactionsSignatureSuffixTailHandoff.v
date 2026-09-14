Require Import ZesuSsz.Automation.All.
Require Import ZesuSsz.Automation.RegPacking.
Require Import ZesuSsz.Automation.Resources.
Require Import isla.riscv64.riscv64.
From ZesuSsz.Proofs.WriteSuccess Require Import
  WriteSuccessExactTransactionsSignatureLowWideEntry WriteSuccessExactTransactionsRecipientWide
  WriteSuccessExactTransactionsSignatureSuffix WriteSuccessExactTransactionsSignatureTail
  WriteSuccessExactTransactionsValueMiddleWordsEntry WriteSuccessExactTransactionsRecipientTagShiftEntry
  WriteSuccessExactTransactionsSignatureFieldEntry WriteSuccessExactTransactionsGasSignatureEntry
  WriteSuccessExactTransactionsGasLoads WriteSuccessExactTransactionsFlagLoads.
Local Open Scope Z_scope.

From ZesuSsz.Proofs.WriteSuccess Require Import
  WriteSuccessExactTransactionsWideSignatureSuffixSpec.

Lemma transactions_signature_suffix_tail_entry `{!islaG Sigma} `{!threadG}
    sp row chain chainTag base bytes index (P : iProp Sigma) :
  transactionSignatureSuffixPost sp row base bytes index
    (transactionSignatureSuffixRetained sp row chain chainTag bytes index (transactionSignatureTailCaller sp P)) -∗
  transactionSignatureTailEntry sp row base bytes index
    (transactionSignatureTailRetained sp row chain chainTag bytes index P).
Proof.
  iStartProof. iIntros "Hpost".
  iEval (rewrite /transactionSignatureSuffixPost) in "Hpost".
  iDestruct "Hpost" as "(Hsys & Hsp & Hrow & H15 & Hframe)".
  iPoseProof (reg_col_bv_list_shape [("x15", transactionRowWord bytes index 112)]
    with "[H15]") as "Hregs".
  { cbn. iFrame. }
  iEval (rewrite /transactionSignatureSuffixRetained /transactionRecipientWideRegisters
    /transactionSignatureStackFrame /transactionRecipientAssemblyStackContents
    /transactionRecipientAssemblyFields /transactionSignatureFieldRetained
    /transactionGasSignatureRetained /transactionSignatureTailCaller) in "Hframe".
  zesu_open_resource_groups.
  rewrite /transactionSignatureTailEntry /transactionSignatureTailRetained /transactionSignatureSuffixRetained
    /transactionRecipientWideRegisters /transactionSignatureStackFrame /transactionRecipientAssemblyStackContents
    /transactionRecipientAssemblyFields /transactionSignatureFieldRetained /transactionGasSignatureRetained.
  iFrame. repeat iSplit; try done; iPureIntro; lia.
Qed.
Print Assumptions transactions_signature_suffix_tail_entry.

