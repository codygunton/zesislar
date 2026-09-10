From Coq Require Import Lists.List ZArith.ZArith.
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Contracts.IslarisMachine.
Require Import ZesuSsz.Experiments.WriteSuccessTransactionsBoundarySpec.
Require Import ZesuSsz.Experiments.WriteSuccessTransactionsSpec.

Definition writeSuccessTransactionsLoopEntryFacts
    (sp : bv 64) (base : Z)
    (processed remaining : list writeSuccessTransaction) : Prop :=
  writeSuccessTransactionsBytes (processed ++ remaining) =
    writeSuccessTransactionsBytes processed ++
      writeSuccessTransactionsBytes remaining /\
  length (writeSuccessTransactionsBytes (processed ++ remaining)) =
    (288 * length (processed ++ remaining))%nat /\
  length (writeSuccessTransactionsBytes processed) =
    (288 * length processed)%nat /\
  length (writeSuccessTransactionsBytes remaining) =
    (288 * length remaining)%nat /\
  (length (processed ++ remaining) < 2 ^ 64)%nat /\
  bv_unsigned sp `mod` 16 = 0 /\
  0x20000000 <= bv_unsigned sp - 48 /\
  bv_unsigned sp + 1896 < 0x40000000 /\
  base `mod` 8 = 0 /\
  0x20000000 <= base /\
  base + Z.of_nat
    (length (writeSuccessTransactionsBytes (processed ++ remaining))) <
      0x40000000.

Definition writeSuccessTransactionsLoopBodyBranchFrame `{!islaG Sigma}
    `{!threadG} (P : iProp Sigma) (sp : bv 64) (base : Z)
    (processed remaining : list writeSuccessTransaction) (tail : spec) :
    iProp Sigma :=
  (reg_col zesu_ram_sys_regs ∗
   reg_col writeSuccessTransactionsOtherRegShapes ∗
   "x2" ↦ᵣ RVal_Bits sp ∗
   "x10" ↦ᵣ RVal_Bits
      (Z_to_bv 64 (Z.of_nat (length (processed ++ remaining)))) ∗
   "x11" ↦ᵣ RVal_Bits (Z_to_bv 64 (Z.of_nat (length processed))) ∗
   base ↦ₘ∗ writeSuccessTransactionsBytes processed ∗
   (base + 288 * Z.of_nat (length processed)) ↦ₘ∗
      writeSuccessTransactionsBytes remaining ∗
   writeSuccessTransactionsOwn processed ∗
   writeSuccessTransactionsOwn remaining ∗
   (bv_unsigned sp - 48) ↦ₘ? 152 ∗
   (bv_unsigned sp + 104) ↦ₘ Z_to_bv 64 base ∗
   (bv_unsigned sp + 112) ↦ₘ
      Z_to_bv 64 (Z.of_nat (length (processed ++ remaining))) ∗
   (bv_unsigned sp + 120) ↦ₘ? 1776 ∗
   mmio_range 0x2401a0c0 16 ∗
   spec_trace (writeSuccessTransactionsEvents sp remaining tail) ∗ P ∗
   instr_pre writeSuccessTransactionsLoopExitAddress
     (writeSuccessTransactionsLoopExit sp base (processed ++ remaining)
       (writeSuccessTransactionsBytes (processed ++ remaining)) tail P) ∗ True)%I.

Global Instance : LithiumUnfold
    (@writeSuccessTransactionsLoopBodyBranchFrame) := I.

Lemma write_success_transactions_loop_entry_body
    `{!islaG Sigma} `{!threadG} (P : iProp Sigma) (sp : bv 64) (base : Z)
    (processed remaining : list writeSuccessTransaction) (tail : spec)
    (Hfacts : writeSuccessTransactionsLoopEntryFacts
      sp base processed remaining)
    (Hneq : Z_to_bv 64 (Z.of_nat (length processed)) <>
      Z_to_bv 64 (Z.of_nat (length (processed ++ remaining)))) :
  writeSuccessTransactionsLoopBodyBranchFrame
      P sp base processed remaining tail -∗
  writeSuccessTransactionsAt14f08Spec P.
Proof.
  destruct remaining as [|transaction remaining].
  { rewrite app_nil_r in Hneq. contradiction. }
  iIntros "Hframe".
  iDestruct "Hframe" as
    "(Hsys & Hother & H2 & H10 & H11 & Hprefix & Hsuffix & Hprocessed &
      Hremaining & Hlower & Hbase & Htotal & Hupper & Hmmio & Hevents & HP &
      Hexit & _)".
  iDestruct "Hremaining" as "(Htransaction & Hremaining & _)".
  iExists sp, base, transaction, (processed ++ transaction :: remaining),
    processed, remaining,
    (writeSuccessTransactionsBytes (processed ++ transaction :: remaining)),
    (writeSuccessTransactionsBytes processed),
    (writeSuccessTransactionsBytes (transaction :: remaining)), tail.
  rewrite /writeSuccessTransactionPhaseHandoff
    /writeSuccessTransactionsMachine14f08.
  iSplitL "Hsys Hother H2 H10 H11 Hlower Hbase Htotal Hupper".
  { rewrite /writeSuccessTransactionsScratch.
    iFrame "Hsys Hother H2 H10 H11 Hlower Hbase Htotal Hupper". }
  iFrame "Hprefix Hsuffix Htransaction Hremaining Hmmio HP Hexit".
  iSplitL "Hprocessed".
  { rewrite /writeSuccessTransactionsProcessedOwn. iExact "Hprocessed". }
  iSplitL "Hevents".
  { iExact "Hevents". }
  rewrite /writeSuccessTransactionsInvariant
    /writeSuccessTransactionsLoopEntryFacts in Hfacts.
  destruct Hfacts as
    (Hbytes & Hlength & HprefixLength & HsuffixLength & Hbound & HspAlign &
      HspLow & HspHigh & HbaseAlign & HbaseLow & HbaseHigh).
  repeat iSplit; try iPureIntro; try assumption; try reflexivity.
Qed.
