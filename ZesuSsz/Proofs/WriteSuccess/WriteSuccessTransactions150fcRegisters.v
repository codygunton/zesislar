Require Import ZesuSsz.Automation.AllLegacy.
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Contracts.IslarisMachine.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessTransactionsBoundary15104.

Lemma write_success_transactions_150fc_registers `{!islaG Sigma} `{!threadG} :
  reg_col
    [(KindReg "x3", BitsShape 64); (KindReg "x4", BitsShape 64);
     (KindReg "x5", BitsShape 64); (KindReg "x6", BitsShape 64);
     (KindReg "x7", BitsShape 64); (KindReg "x11", BitsShape 64);
     (KindReg "x12", BitsShape 64); (KindReg "x13", BitsShape 64);
     (KindReg "x14", BitsShape 64); (KindReg "x15", BitsShape 64);
     (KindReg "x16", BitsShape 64); (KindReg "x17", BitsShape 64);
     (KindReg "x28", BitsShape 64); (KindReg "x29", BitsShape 64);
     (KindReg "x30", BitsShape 64); (KindReg "x31", BitsShape 64)] -∗
  reg_col writeSuccessTransactions15104OtherRegShapes ∗
  ("x5" ↦ᵣ: fun r5 => ⌜valu_has_shape r5 (BitsShape 64)⌝) ∗
  ("x11" ↦ᵣ: fun r11 => ⌜valu_has_shape r11 (BitsShape 64)⌝).
Proof. move => *. zesu_block. Qed.
