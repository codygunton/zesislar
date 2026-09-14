Require Import ZesuSsz.Automation.All.
Require Import isla.riscv64.riscv64.
From IslaTraces.main Require Import instrs.
Require Import ZesuSsz.Proofs.Main.Resources.

Definition mainPrologueInstrs : list (Z * isla_trace) :=
  [(0x14cb0, a14cb0); (0x14cb4, a14cb4); (0x14cb8, a14cb8);
   (0x14cbc, a14cbc); (0x14cc0, a14cc0); (0x14cc4, a14cc4);
   (0x14cc8, a14cc8)].

Lemma main_prologue_correct `{!islaG Sigma} `{!threadG}
    (sp ra a0 a1 saved size : bv 64) :
  ([∗ list] i ∈ mainPrologueInstrs, instr i.1 (Some i.2)) -∗
  instr_body 0x10140 (mainReadInputCall sp ra) -∗
  instr_body 0x14cb0 (mainPrologueEntry sp ra a0 a1 saved size).
Proof.
  unfold mainPrologueInstrs, mainPrologueEntry, mainReadInputCall, mainFrameSp.
  zesu_block.
Qed.
Print Assumptions main_prologue_correct.

Lemma main_prologue_correct_with_frame `{!islaG Sigma} `{!threadG}
    (sp ra a0 a1 saved size : bv 64) (P : iProp Sigma) :
  ([∗ list] i ∈ mainPrologueInstrs, instr i.1 (Some i.2)) -∗
  instr_body 0x10140 (mainReadInputCall sp ra ∗ P ∗ True) -∗
  instr_body 0x14cb0 (mainPrologueEntry sp ra a0 a1 saved size ∗ P ∗ True).
Proof.
  unfold mainPrologueInstrs, mainPrologueEntry, mainReadInputCall, mainFrameSp.
  zesu_block.
Qed.
Print Assumptions main_prologue_correct_with_frame.
