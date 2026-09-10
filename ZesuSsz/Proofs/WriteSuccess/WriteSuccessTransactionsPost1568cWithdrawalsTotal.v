Require Import ZesuSsz.Automation.All.
From Coq Require Import ZArith.ZArith.
Require Import isla.riscv64.riscv64.
From IslaTraces.write_success_blocks Require Import Index.
Require Import ZesuSsz.Contracts.IslarisCode.
Require Import ZesuSsz.Contracts.IslarisMachine.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessTransactionsPost1568c.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessTransactionsPostWithdrawalsHandoff.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessTransactionsWithdrawalsTotalBranch.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessTransactionsWithdrawalsTotalTailState.

Lemma write_success_transactions_post_1568c_withdrawals_total
    `{!islaG Sigma} `{!threadG} (P : iProp Sigma) :
  instr_lookup_resources IslaTraces.write_success_blocks.Index.lookup -∗
  □ instr_pre 0x15694 (writeSuccessTransactionsPostWithdrawalsHandoff P) -∗
  instr_body 0x1568c
    (writeSuccessTransactionsWithdrawalsTotalAt1568cSpec P).
Proof.
  iStartProof. iIntros "#Hlookup #Hloop".
  rewrite instr_pre'_eq. iIntros "Hentry".
  iEval (rewrite /writeSuccessTransactionsWithdrawalsTotalAt1568cSpec) in "Hentry".
  iDestruct "Hentry" as (sp pointer base count bytes tail)
    "(Hsys & H2 & H18 & Hrest)".
  iPoseProof (write_success_transactions_withdrawals_total_branch P with
    "Hlookup [Hloop]") as "Hbranch".
  { iEval (rewrite -instr_pre'_eq) in "Hloop". iExact "Hloop". }
  iAssert (instr_body 0x15690
    (reg_col zesu_ram_sys_regs ∗ "x2" ↦ᵣ RVal_Bits sp ∗
     "x18" ↦ᵣ RVal_Bits (sp + BV 64 1768)%bv ∗
     writeSuccessTransactionsWithdrawalsTotalAt1568cRest P sp pointer base
       count bytes tail))%I with "[Hbranch]" as "Hnext".
  { iApply (instr_pre_wand 0x15690 0x15690 false false with "Hbranch");
      [done | done |].
    iIntros "Hpost".
    iDestruct "Hpost" as "(HsysPost & H2Post & H18Post & HrestPost)".
    iEval (rewrite /writeSuccessTransactionsWithdrawalsTotalAt1568cRest)
      in "HrestPost".
    iDestruct "HrestPost" as
      "(Hother & H8 & H9 & Hscratch & Hmmio & Htrace & Hresources & _)".
    iEval (rewrite /writeSuccessTransactionsWithdrawalsTotalAt15690Spec).
    iExists sp, pointer, base, count, bytes, tail.
    iFrame "HsysPost Hother H2Post H8 H9 H18Post Hscratch Hmmio Htrace
      Hresources". }
  iPoseProof (write_success_transactions_post_1568c_addi sp
    (writeSuccessTransactionsWithdrawalsTotalAt1568cRest P sp pointer base
      count bytes tail) with "Hlookup Hnext") as "Haddi".
  iEval (rewrite instr_pre'_eq) in "Haddi".
  iDestruct ("Haddi" with "[Hsys H2 H18 Hrest]") as (ins) "(Hinstr & Hwp)".
  { iFrame "Hsys H2 H18 Hrest". }
  iExists ins. iFrame "Hinstr". iExact "Hwp".
Qed.
