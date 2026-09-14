Require Import ZesuSsz.Automation.All.
Require Import ZesuSsz.Automation.CodeLookup.
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Contracts.IslarisMachine.
From ZesuSsz.Proofs.WriteSuccess Require Import
  WriteSuccessNativeCode WriteSuccessExactBlobHashesEmpty.

(** The zero count leaves the pointer unused. The caller keeps the pointer
    and every payload resource in [P]. *)
Lemma transactions_blob_empty_region_correct `{!islaG Sigma} `{!threadG}
    (P : iProp Sigma) :
  writeSuccessCompleteNativeCode -∗
  instr_body 0x15564
    (reg_col zesu_ram_sys_regs ∗ "x22" ↦ᵣ RVal_Bits (BV 64 0) ∗ P ∗ True)%I -∗
  instr_body 0x153d0
    (reg_col zesu_ram_sys_regs ∗ "x22" ↦ᵣ RVal_Bits (BV 64 0) ∗ P ∗ True)%I.
Proof.
  iStartProof. iIntros "#Hcode Hnext".
  iEval (unfold writeSuccessCompleteNativeCode) in "Hcode".
  iDestruct "Hcode" as
    "#(Hprologue & Hlookup & Hmain & Houtput & Hmemcpy & Hboolean & Hoptional & HbyteLists & Hbytes & Hint & Hu256 & Hu128)".
  iApply (blob_initial_empty with "[] Hnext").
  iApply instr_lookup_collect; last iExact "Hlookup".
  repeat constructor; reflexivity.
Qed.
Print Assumptions transactions_blob_empty_region_correct.
