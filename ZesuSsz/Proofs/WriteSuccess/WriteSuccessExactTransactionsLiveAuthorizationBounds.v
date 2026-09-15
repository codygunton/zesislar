Require Import ZesuSsz.Automation.All.
Require Import isla.riscv64.riscv64.
From ZesuSsz.Proofs.WriteSuccess Require Import
 WriteSuccessTransactionsSpec WriteSuccessExactTransactionsLiveSpec
 WriteSuccessExactTransactionsOwnership.

Lemma transactions_live_authorization_bounds `{!islaG Sigma} `{!threadG}
 sp base transactions processed transaction rest bytes tail (P : iProp Sigma) :
 writeSuccessTransactionAuthorizationBytes transaction <> [] ->
 transactionLiveLoopState sp base transactions processed (transaction :: rest) bytes tail P -∗
 ⌜mapRamBase defaultMap <=
    bv_unsigned (writeSuccessTransactionAuthorizationPointer transaction)⌝ ∗
 ⌜bv_unsigned (writeSuccessTransactionAuthorizationPointer transaction) +
    Z.of_nat (length (writeSuccessTransactionAuthorizationBytes transaction)) <
    machineRamEnd defaultMap⌝ ∗
 transactionLiveLoopState sp base transactions processed (transaction :: rest) bytes tail P.
Proof.
 intros Hnonempty.
 iIntros "(Hsys & Hregs & Hsp & H10 & H11 & Hbytes & Hown & Hscratch &
   Hmmio & Htrace & %Hfacts & HP & _)".
 have Hrelation := proj1 Hfacts.
 iEval (rewrite Hrelation transactions_own_app) in "Hown".
 iDestruct "Hown" as "(Hprocessed & Hremaining & _)".
 cbn [writeSuccessTransactionsOwn].
 iDestruct "Hremaining" as
   "((Hdata & Haccess & Hentries & Hblob & Hauth & %Hvalid & _) & Hrest & _)".
 destruct (writeSuccessTransactionAuthorizationBytes transaction)
   as [|byte authBytes] eqn:HauthBytes; first contradiction.
 iEval (unfold writeSuccessByteArrayOwn) in "Hauth".
 iDestruct "Hauth" as "(Hauth & %Hlow & %Hhigh & _)".
 iSplit; first done. iSplit; first done.
 unfold transactionLiveLoopState. iFrame.
 iSplitL "Hprocessed Hdata Haccess Hentries Hblob Hauth Hrest".
 { rewrite Hrelation transactions_own_app /=.
   iSplitL "Hprocessed"; first iExact "Hprocessed".
   iSplitL "Hdata Haccess Hentries Hblob Hauth Hrest".
   { iSplitL "Hdata Haccess Hentries Hblob Hauth".
     { unfold writeSuccessTransactionOwn.
     iSplitL "Hdata"; first iExact "Hdata".
     iSplitL "Haccess"; first iExact "Haccess".
     iSplitL "Hentries"; first iExact "Hentries".
     iSplitL "Hblob"; first iExact "Hblob".
     iSplitL "Hauth".
     { rewrite /writeSuccessByteArrayOwn HauthBytes.
       iFrame. repeat iSplit; try done. }
     iSplit; first done. done. }
     iFrame. }
   done. }
 done.
Qed.
Print Assumptions transactions_live_authorization_bounds.
