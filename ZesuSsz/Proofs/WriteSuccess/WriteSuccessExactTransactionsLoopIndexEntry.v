Require Import ZesuSsz.Automation.All.
Require Import ZesuSsz.Automation.UninitRegions.
Require Import isla.riscv64.riscv64.
From ZesuSsz.Proofs.WriteSuccess Require Import
  WriteSuccessExactTransactionsSpec WriteSuccessTransactionsSpec
  WriteSuccessExactTransactionsIndexCell WriteSuccessExactTransactionsIndexSourceEntry
  WriteSuccessExactTransactionsTypeTailModel WriteSuccessExactTransactionsRowByte
  WriteSuccessExactTransactionsLayout WriteSuccessExactTransactionsLiveSpec.
Local Open Scope Z_scope.

Definition transactionLoopSourceFrame `{!islaG Sigma} `{!threadG}
    (sp : bv 64) (base : Z) (transactions processed remaining : list writeSuccessTransaction)
    (bytes : list (bv 8)) (P : iProp Sigma) : iProp Sigma :=
  ((bv_unsigned sp - 48) ↦ₘ? 48 ∗
   (bv_unsigned sp + 112) ↦ₘ Z_to_bv 64 (Z.of_nat (length transactions)) ∗
   writeSuccessTransactionsOwn transactions ∗
   ⌜transactionLoopSourceFacts sp base transactions processed remaining bytes⌝ ∗ P ∗ True)%I.
Global Instance : LithiumUnfold (@transactionLoopSourceFrame) := I.

Lemma transactions_loop_to_index `{!islaG Sigma} `{!threadG}
    sp base transactions processed transaction rest bytes tail (P : iProp Sigma) :
  transactionLiveLoopState sp base transactions processed (transaction :: rest)
    bytes tail P -∗
  transactionIndexCellEntry sp (Z_to_bv 64 base)
    (Z_to_bv 64 (Z.of_nat (length processed)))
    (Z_to_bv 64 (Z.of_nat (length transactions)))
    (transactionIndexSourceCaller sp base bytes (length processed)
      (writeSuccessExactTransactionAfterTypeEvents sp transaction
        (writeSuccessExactTransactionsEvents sp rest tail))
      (transactionLoopSourceFrame sp base transactions processed (transaction :: rest) bytes P)).
Proof.
  iStartProof. iIntros "Hstate".
  iEval (unfold transactionLiveLoopState, transactionLiveScratch) in "Hstate".
  iDestruct "Hstate" as "(Hsys & Hregs & Hsp & H10 & H11 & Hbytes & Hown & (Hlower & HbaseWord & Htotal & Hscratch & HsourceScratch & _) & Hmmio & Htrace & %Hfacts & HP & _)".
  have HfactsCopy := Hfacts.
  destruct HfactsCopy as (Htransactions & Hbytes & Hlength & Hcount & HspAlign & Hlow & Hhigh & HbaseAlign & Hbase & Hend).
  iDestruct (exact_transactions_own_valid with "Hown") as "(Hown & %Hvalid & _)".
  rewrite Htransactions in Hvalid. apply Forall_app in Hvalid as [Hprefix Hremaining].
  have Htransaction := Forall_inv Hremaining.
  have Htype := exact_transaction_row_byte processed transaction rest 264 Hprefix Htransaction ltac:(repeat constructor).
  rewrite -Htransactions -Hbytes in Htype.
  have HtypeValid := proj1 (proj2 Htransaction).
  have Hindex : (288 * length processed + 288 <= length bytes)%nat.
  { clear -Hlength Htransactions. rewrite Hlength Htransactions app_length /=. lia. }
  have Hsp8 : bv_unsigned sp `mod` 8 = 0.
  { clear -HspAlign. apply Z.mod_divide; first lia. apply Z.divide_trans with 16; first (exists 2; reflexivity).
    apply Z.mod_divide; [lia | exact HspAlign]. }
  have HspLow : 0x20000000 <= bv_unsigned sp by (clear -Hlow; lia).
  iEval (rewrite (transactions_exact_type_tail sp transaction rest tail) -HtypeValid -Htype) in "Htrace".
  iAssert (∃ _ : unit, transactionIndexCellEntry sp (Z_to_bv 64 base)
    (Z_to_bv 64 (Z.of_nat (length processed)))
    (Z_to_bv 64 (Z.of_nat (length transactions)))
    (transactionIndexSourceCaller sp base bytes (length processed)
      (writeSuccessExactTransactionAfterTypeEvents sp transaction
        (writeSuccessExactTransactionsEvents sp rest tail))
      (transactionLoopSourceFrame sp base transactions processed (transaction :: rest) bytes P)) ∗ True)%I
    with "[Hsys Hregs Hsp H10 H11 Hbytes Hown Hlower HbaseWord Htotal Hscratch HsourceScratch Hmmio Htrace HP]" as "Hentry".
  { zesu_run. }
  iDestruct "Hentry" as (_) "[Hentry _]". iExact "Hentry".
Qed.
Print Assumptions transactions_loop_to_index.
