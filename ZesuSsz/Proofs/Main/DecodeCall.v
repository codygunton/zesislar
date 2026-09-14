Require Import ZesuSsz.Automation.All.
Require Import isla.riscv64.riscv64.
From IslaTraces.main Require Import instrs.
Require Import ZesuSsz.Proofs.Main.Resources.

Definition mainDecodeCallInstrs : list (Z * isla_trace) :=
  [(0x14cec, a14cec); (0x14cf0, a14cf0); (0x14cf4, a14cf4);
   (0x14cf8, a14cf8)].

Lemma main_decode_call_correct `{!islaG Sigma} `{!threadG}
    (sp ra a0 a1 : bv 64) :
  ([∗ list] i ∈ mainDecodeCallInstrs, instr i.1 (Some i.2)) -∗
  instr_body 0x12168
    (mainCallRegisters sp (BV 64 0x14cfc)
      (sp + BV 64 32)%bv (sp + BV 64 16)%bv) -∗
  instr_body 0x14cec (mainCallRegisters sp ra a0 a1).
Proof. unfold mainDecodeCallInstrs. zesu_block. Qed.
Print Assumptions main_decode_call_correct.

Lemma main_decode_call_correct_with_frame `{!islaG Sigma} `{!threadG}
    (sp ra a0 a1 : bv 64) (P : iProp Sigma) :
  ([∗ list] i ∈ mainDecodeCallInstrs, instr i.1 (Some i.2)) -∗
  instr_body 0x12168
    (mainCallRegisters sp (BV 64 0x14cfc)
      (sp + BV 64 32)%bv (sp + BV 64 16)%bv ∗ P ∗ True) -∗
  instr_body 0x14cec (mainCallRegisters sp ra a0 a1 ∗ P ∗ True).
Proof. unfold mainDecodeCallInstrs. zesu_block. Qed.
Print Assumptions main_decode_call_correct_with_frame.
