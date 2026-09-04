From Coq Require Import Lists.List ZArith.ZArith.
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Contracts.IslarisMachine.
Require Import ZesuSsz.Experiments.WriteSuccessTransactionsBoundary15088.

Definition writeSuccessTransactions15088LoadMachineFrame
    `{!islaG Sigma} `{!threadG} (sp : bv 64) (base : Z)
    (transactions processed :
      list WriteSuccessTransactionsSpec.writeSuccessTransaction)
    (transaction : WriteSuccessTransactionsSpec.writeSuccessTransaction) :
    iProp Sigma :=
  (∀ x15 : valu,
    reg_col zesu_ram_sys_regs -∗
    "x15" ↦ᵣ x15 -∗
    "x10" ↦ᵣ RVal_Bits
      (Z_to_bv 64 (base + 288 * Z.of_nat (length processed))) -∗
    writeSuccessTransactionsMachine15088WithX15
      sp base transactions processed transaction x15)%I.

Global Instance : LithiumUnfold
    (@writeSuccessTransactions15088LoadMachineFrame) := I.

Lemma write_success_transactions_chunk_15088_load_frame
    `{!islaG Sigma} `{!threadG} (sp : bv 64) (base : Z)
    (transactions processed :
      list WriteSuccessTransactionsSpec.writeSuccessTransaction)
    (transaction : WriteSuccessTransactionsSpec.writeSuccessTransaction)
    (x15 : valu) :
  writeSuccessTransactionsMachine15088WithX15
    sp base transactions processed transaction x15 -∗
  reg_col zesu_ram_sys_regs ∗
  "x15" ↦ᵣ x15 ∗
  "x10" ↦ᵣ RVal_Bits
    (Z_to_bv 64 (base + 288 * Z.of_nat (length processed))) ∗
  writeSuccessTransactions15088LoadMachineFrame
    sp base transactions processed transaction.
Proof.
  rewrite /writeSuccessTransactionsMachine15088WithX15.
  iIntros "(Hsys & Hother & Hx2 & Hx5 & Hx6 & Hx7 & Hx8 & Hx9 & Hx10 &
    Hx11 & Hx12 & Hx13 & Hx14 & Hx15 & Hx16 & Hx17 & Hx18 & Hx19 & Hx20 &
    Hx21 & Hx23 & Hx24 & Hx25 & Hx26 & Hx27 & Hx28 & Hx29 & Hx30 & Hx31 &
    Hscratch & _)".
  iFrame "Hsys Hx15 Hx10".
  iIntros (newX15) "Hsys Hx15 Hx10".
  rewrite /writeSuccessTransactionsMachine15088WithX15.
  iFrame.
Qed.
