Require Import ZesuSsz.Automation.All.
Require Import ZesuSsz.Automation.TraceResume.
Require Import isla.riscv64.riscv64.
Lemma test_trace_resume `{!islaG Sigma} `{!threadG} :
  instr_pre 0x10000 True -∗ "PC" ↦ᵣ RVal_Bits (BV 64 0x10000) -∗
  WPasm (TRACE_LET tnil).
Proof. iStartProof. iIntros "Hpre Hpc". zesu_resume. Qed.
Print Assumptions test_trace_resume.
