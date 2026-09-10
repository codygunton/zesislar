From Coq Require Import Lists.List ZArith.ZArith.
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Contracts.IslarisMachine.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessTransactionsBoundary1519c.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessTransactionsBoundary151a8.

Definition writeSuccessTransactions151a4LoadMachineFrame
    `{!islaG Sigma} `{!threadG} (sp : bv 64) (base : Z)
    (transactions processed :
      list WriteSuccessTransactionsSpec.writeSuccessTransaction)
    (transaction : WriteSuccessTransactionsSpec.writeSuccessTransaction) :
    iProp Sigma :=
  (reg_col zesu_ram_sys_regs -∗
   "x12" ↦ᵣ RVal_Bits (bv_sign_extend 64
     (WriteSuccessTransactionsSpec.writeSuccessTransactionWord transaction 64)) -∗
   "x2" ↦ᵣ RVal_Bits sp -∗
   (bv_unsigned sp + 128) ↦ₘ
     WriteSuccessTransactionsSpec.writeSuccessTransactionWord transaction 64 -∗
   writeSuccessTransactionsMachine151a8 sp base transactions processed
     transaction)%I.

Global Instance : LithiumUnfold
    (@writeSuccessTransactions151a4LoadMachineFrame) := I.

Lemma write_success_transactions_151a4_load_machine_frame
    `{!islaG Sigma} `{!threadG} (sp : bv 64) (base : Z)
    (transactions processed :
      list WriteSuccessTransactionsSpec.writeSuccessTransaction)
    (transaction : WriteSuccessTransactionsSpec.writeSuccessTransaction) :
  writeSuccessTransactionsMachine151a4 sp base transactions processed transaction -∗
  reg_col zesu_ram_sys_regs ∗
  ("x12" ↦ᵣ: fun _ => True) ∗
  "x2" ↦ᵣ RVal_Bits sp ∗
  (bv_unsigned sp + 128) ↦ₘ
    WriteSuccessTransactionsSpec.writeSuccessTransactionWord transaction 64 ∗
  writeSuccessTransactions151a4LoadMachineFrame sp base transactions processed
    transaction.
Proof.
  rewrite /writeSuccessTransactionsMachine151a4
    /writeSuccessTransactionsScratch1519c.
  iIntros "(Hsys & Hother & H2 & H5 & H8 & H9 & H10 & H11 & H18 & H19 &
    H20 & H21 & H22 & H23 & H24 & H25 & H26 & H27 & Hscratch & _)".
  iEval (rewrite !reg_col_cons reg_col_nil) in "Hother".
  iDestruct "Hother" as
    "(H1 & H3 & H4 & H6 & H7 & H12 & H13 & H14 & H15 & H16 & H17 &
      H28 & H29 & H30 & H31)".
  iDestruct "H12" as (oldX12) "(%H12shape & H12)".
  iDestruct "Hscratch" as
    "(Hs48 & Hs104 & Hs112 & Hs120 & Hs128 & Hs136 & Hs144 & Hs152 &
      Hs160 & Hs168 & Hs176 & Hs184 & Hs192 & Hs200 & Hs208 & Hs216 &
      Hs224 & Hs232 & Hs240 & Hs248 & Hs256 & Hs264 & Hs272 & Hs280 &
      Hs1640 & Hs1648 & Hs1656 & Hs1660 & Hs1664 & Hs1672 & Hs1680 &
      HsTo & _)".
  iAssert (("x12" ↦ᵣ: fun _ => True))%I with "[H12]" as "H12any".
  { rewrite reg_mapsto_pred_eq /reg_mapsto_pred_def.
    iExists oldX12. iSplit; first iExact "H12". done. }
  iFrame "Hsys H12any H2 Hs128".
  iIntros "Hsys H12 H2 Hs128".
  rewrite /writeSuccessTransactionsMachine151a8
    /writeSuccessTransactionsScratch1519c.
  iSplitL "Hsys"; first iExact "Hsys".
  iEval (rewrite !reg_col_cons reg_col_nil).
  iFrame "H1 H3 H4 H6 H7 H13 H14 H15 H16 H17 H28 H29 H30 H31 H2 H5
    H8 H9 H10 H11 H12 H18 H19 H20 H21 H22 H23 H24 H25 H26 H27 Hs48 Hs104
    Hs112 Hs120 Hs128 Hs136 Hs144 Hs152 Hs160 Hs168 Hs176 Hs184 Hs192 Hs200
    Hs208 Hs216 Hs224 Hs232 Hs240 Hs248 Hs256 Hs264 Hs272 Hs280 Hs1640 Hs1648
    Hs1656 Hs1660 Hs1664 Hs1672 Hs1680 HsTo".
Qed.

Definition writeSuccessTransactions151a4Outer
    `{!islaG Sigma} `{!threadG} (P : iProp Sigma)
    (sp : bv 64) (base : Z)
    (transaction : WriteSuccessTransactionsSpec.writeSuccessTransaction)
    (transactions processed remaining :
      list WriteSuccessTransactionsSpec.writeSuccessTransaction)
    (bytes prefix suffix : list (bv 8)) (tail : spec) : iProp Sigma :=
  WriteSuccessTransactionsSpec.writeSuccessTransactionPhaseHandoff
    WriteSuccessTransactionsSpec.TransactionValue True sp base transaction
    transactions processed remaining bytes prefix suffix tail P.

Global Instance : LithiumUnfold (@writeSuccessTransactions151a4Outer) := I.

Definition writeSuccessTransactionsAt151a4Block
    `{!islaG Sigma} `{!threadG} (P : iProp Sigma)
    (sp : bv 64) (base : Z)
    (transaction : WriteSuccessTransactionsSpec.writeSuccessTransaction)
    (transactions processed remaining :
      list WriteSuccessTransactionsSpec.writeSuccessTransaction)
    (bytes prefix suffix : list (bv 8)) (tail : spec) : iProp Sigma :=
  (⌜bv_extract 0 3 (sp + 128) = 0%bv⌝ ∗
   ⌜0x20000000 <= bv_unsigned (sp + 128)⌝ ∗
   ⌜bv_unsigned (sp + 128) <= 0x20000000 + 0x20000000 - 8⌝ ∗
   WriteSuccessTransactionsSpec.writeSuccessTransactionPhaseHandoff
     WriteSuccessTransactionsSpec.TransactionValue
     (writeSuccessTransactionsMachine151a4 sp base transactions processed
       transaction)
     sp base transaction transactions processed remaining bytes prefix suffix
     tail P)%I.

Global Instance : LithiumUnfold (@writeSuccessTransactionsAt151a4Block) := I.

Definition writeSuccessTransactions151a4LoadState
    `{!islaG Sigma} `{!threadG} (P : iProp Sigma)
    (sp : bv 64) (base : Z)
    (transaction : WriteSuccessTransactionsSpec.writeSuccessTransaction)
    (transactions processed remaining :
      list WriteSuccessTransactionsSpec.writeSuccessTransaction)
    (bytes prefix suffix : list (bv 8)) (tail : spec) : iProp Sigma :=
  (reg_col zesu_ram_sys_regs ∗
   ("x12" ↦ᵣ: fun _ => True) ∗
   "x2" ↦ᵣ RVal_Bits sp ∗
   (bv_unsigned sp + 128) ↦ₘ
     WriteSuccessTransactionsSpec.writeSuccessTransactionWord transaction 64 ∗
   writeSuccessTransactions151a4LoadMachineFrame sp base transactions processed
     transaction ∗
   writeSuccessTransactions151a4Outer P sp base transaction transactions
     processed remaining bytes prefix suffix tail ∗
   ⌜bv_unsigned sp `mod` 16 = 0⌝ ∗
   ⌜0x20000000 <= bv_unsigned sp - 48⌝ ∗
   ⌜bv_unsigned sp + 1896 < 0x40000000⌝ ∗
   ⌜bv_extract 0 3 (sp + 128) = 0%bv⌝ ∗
   ⌜0x20000000 <= bv_unsigned (sp + 128)⌝ ∗
   ⌜bv_unsigned (sp + 128) <= 0x20000000 + 0x20000000 - 8⌝ ∗ True)%I.

Definition writeSuccessTransactions151a4LoadResult
    `{!islaG Sigma} `{!threadG} (P : iProp Sigma)
    (sp : bv 64) (base : Z)
    (transaction : WriteSuccessTransactionsSpec.writeSuccessTransaction)
    (transactions processed remaining :
      list WriteSuccessTransactionsSpec.writeSuccessTransaction)
    (bytes prefix suffix : list (bv 8)) (tail : spec) : iProp Sigma :=
  (writeSuccessTransactionsMachine151a8 sp base transactions processed
     transaction ∗
   writeSuccessTransactions151a4Outer P sp base transaction transactions
     processed remaining bytes prefix suffix tail ∗
   ⌜bv_extract 0 3 (sp + 128) = 0%bv⌝ ∗
   ⌜0x20000000 <= bv_unsigned (sp + 128)⌝ ∗
   ⌜bv_unsigned (sp + 128) <= 0x20000000 + 0x20000000 - 8⌝ ∗ True)%I.

Global Instance : LithiumUnfold (@writeSuccessTransactions151a4LoadState) := I.
Global Instance : LithiumUnfold (@writeSuccessTransactions151a4LoadResult) := I.
