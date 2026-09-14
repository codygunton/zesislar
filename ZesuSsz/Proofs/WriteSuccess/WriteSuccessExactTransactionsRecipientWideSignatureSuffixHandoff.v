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

Lemma transactions_recipient_wide_signature_suffix_entry `{!islaG Sigma} `{!threadG}
    sp row chain chainTag base bytes index (P : iProp Sigma) :
  transactionRecipientWidePost
    (default (BV 8 0) (bytes !! (index + 265)%nat))
    (default (BV 8 0) (bytes !! (index + 266)%nat))
    (default (BV 8 0) (bytes !! (index + 267)%nat))
    (default (BV 8 0) (bytes !! (index + 268)%nat))
    (default (BV 8 0) (bytes !! (index + 269)%nat))
    (default (BV 8 0) (bytes !! (index + 270)%nat))
    (default (BV 8 0) (bytes !! (index + 271)%nat))
    (default (BV 8 0) (bytes !! (index + 272)%nat))
    (default (BV 8 0) (bytes !! (index + 273)%nat))
    (default (BV 8 0) (bytes !! (index + 274)%nat))
    (default (BV 8 0) (bytes !! (index + 275)%nat))
    (default (BV 8 0) (bytes !! (index + 276)%nat))
    (default (BV 8 0) (bytes !! (index + 277)%nat))
    (default (BV 8 0) (bytes !! (index + 278)%nat))
    (default (BV 8 0) (bytes !! (index + 279)%nat))
    (default (BV 8 0) (bytes !! (index + 280)%nat))
    (transactionRecipientWideFrame sp row chain chainTag base bytes index (transactionSignatureSuffixCaller sp P)) -∗
  transactionSignatureSuffixEntry sp row base bytes index
    (transactionSignatureSuffixRetained sp row chain chainTag bytes index P).
Proof.
  iStartProof. iIntros "Hpost".
  iEval (rewrite /transactionRecipientWidePost) in "Hpost".
  iDestruct "Hpost" as "(Hsys & H12 & H16 & H15 & H13 & Hframe & _)".
  iPoseProof (reg_col_bv_list_shape
    [("x15", Z_to_bv 64 (little_endian_to_bv 8 [(default (BV 8 0) (bytes !! (index + 273)%nat)); (default (BV 8 0) (bytes !! (index + 274)%nat)); (default (BV 8 0) (bytes !! (index + 275)%nat)); (default (BV 8 0) (bytes !! (index + 276)%nat))]))]
    with "[H15]") as "Hregs".
  { cbn. iFrame. }
  iEval (rewrite /transactionRecipientWideFrame /transactionRecipientWideRegisters
    /transactionSignatureAssemblyStorage /transactionRecipientAssemblyStackContents
    /transactionRecipientAssemblyFields /transactionSignatureFieldRetained
    /transactionGasSignatureRetained /transactionSignatureSuffixCaller) in "Hframe".
  zesu_open_resource_groups.
  rewrite /transactionSignatureSuffixEntry /transactionSignatureSuffixRetained
    /transactionRecipientWideRegisters /transactionSignatureStackFrame /transactionRecipientAssemblyStackContents
    /transactionRecipientAssemblyFields /transactionSignatureFieldRetained /transactionGasSignatureRetained.
  iFrame. repeat iSplit; try done; iPureIntro; lia.
Qed.
Print Assumptions transactions_recipient_wide_signature_suffix_entry.

