Require Import ZesuSsz.Automation.AllLegacy.
Require Import ZesuMachineMap.Machine.
From Coq Require Import Lists.List ZArith.ZArith.
Require Import isla.riscv64.riscv64.
From IslaTraces.write_success_blocks Require Import Index.
Require Import ZesuSsz.Contracts.IslarisCode.
Require Import ZesuSsz.Contracts.IslarisMachine.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessTransactionsPost15690Zero.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessTransactionsPost15690Withdrawals.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessTransactionsPostWithdrawalsHandoff.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessTransactionsWithdrawalsPayload.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessTransactionsWithdrawalsTotalNonzero.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessTransactionsWithdrawalsTotalResources.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessWithdrawalsSpec.

Definition writeSuccessTransactionsWithdrawalsTotalAt15690Spec
    `{!islaG Sigma} `{!threadG} (P : iProp Sigma) : iProp Sigma :=
  (∃ (sp pointer : bv 64) (base : Z) (count : nat)
      (bytes : list (bv 8)) (tail : spec),
    reg_col zesu_ram_sys_regs ∗
    reg_col writeSuccessWithdrawalsOtherRegShapes ∗
    "x2" ↦ᵣ RVal_Bits sp ∗ "x8" ↦ᵣ RVal_Bits pointer ∗
    "x9" ↦ᵣ RVal_Bits (Z_to_bv 64 (Z.of_nat count)) ∗
    "x18" ↦ᵣ RVal_Bits (sp + BV 64 1768)%bv ∗
    writeSuccessWithdrawalsScratch sp ∗ mmio_range (machineOutputAddress defaultMap) 16 ∗
    spec_trace (writeSuccessWithdrawalsEvents sp count tail) ∗
    writeSuccessTransactionsWithdrawalsTotalResources P sp pointer base count
      bytes tail ∗ True)%I.

Global Instance : LithiumUnfold
    (@writeSuccessTransactionsWithdrawalsTotalAt15690Spec) := I.

Lemma write_success_transactions_withdrawals_total_branch
    `{!islaG Sigma} `{!threadG} (P : iProp Sigma) :
  instr_lookup_resources IslaTraces.write_success_blocks.Index.lookup -∗
  □ instr_pre 0x15694 (writeSuccessTransactionsPostWithdrawalsHandoff P) -∗
  instr_body 0x15690
    (writeSuccessTransactionsWithdrawalsTotalAt15690Spec P).
Proof.
  iStartProof. iIntros "#Hlookup #Hloop".
  rewrite instr_pre'_eq. iIntros "Hentry".
  iEval (rewrite /writeSuccessTransactionsWithdrawalsTotalAt15690Spec) in "Hentry".
  iDestruct "Hentry" as (sp pointer base count bytes tail)
    "(Hsys & Hother & H2 & H8 & H9 & H18 & Hscratch & Hmmio & Htrace &
      Htotal & _)".
  destruct count as [|remaining].
  - iEval (rewrite /writeSuccessTransactionsWithdrawalsTotalResources) in "Htotal".
    iDestruct "Htotal" as
      "(Hbytes & %Hpointer & %Hlength & %Hcount & %Halign & %Hlower & %Hupper &
        %HbaseLower & %HbaseUpper & Hexit & HP & _)".
    iPoseProof (write_success_transactions_post_15690_zero with "Hlookup")
      as "Hzero".
    iSpecialize ("Hzero" with "[Hexit Hother H2 H8 H18 Hscratch Hmmio Htrace
      Hbytes HP]").
    { iApply (instr_pre_wand 0x156e8 0x156e8 true true with "Hexit");
        [done | done |].
      iIntros "Hpost".
      iDestruct "Hpost" as "(HsysPost & H9Post & _)".
      iEval (rewrite /writeSuccessWithdrawalsLoopExit).
      iExists pointer.
      iEval (rewrite Hpointer) in "Hbytes".
      iFrame "HsysPost Hother H2 H8 H9Post H18 Hbytes Hscratch Hmmio Htrace HP".
      iSplit; last done. iPureIntro.
      rewrite Z.mul_0_r Z.add_0_r. exact Hpointer. }
    iEval (rewrite instr_pre'_eq) in "Hzero".
    iApply "Hzero".
    iEval (rewrite write_success_transactions_zero_bv) in "H9".
    iFrame "Hsys H9".
  - iPoseProof (write_success_transactions_post_15690_withdrawals P with
      "Hlookup [Hloop]") as "Hnonzero".
    { iEval (rewrite -instr_pre'_eq) in "Hloop". iExact "Hloop". }
    iEval (rewrite /writeSuccessWithdrawalsScratch) in "Hscratch".
    iDestruct "Hscratch" as "(HupperScratch & HlowerScratch & _)".
    iPoseProof (write_success_transactions_withdrawals_total_nonzero P
      sp pointer base remaining bytes tail with "HupperScratch Htotal")
      as "Hresources".
    iEval (rewrite /writeSuccessTransactionsWithdrawalsResources) in "Hresources".
    iDestruct "Hresources" as
      "(HupperScratch & Hempty & Hbytes & Hinv & Hexit & HP & _)".
    iEval (rewrite instr_pre'_eq) in "Hnonzero".
    iApply "Hnonzero".
    iEval (rewrite /writeSuccessTransactionsPostWithdrawalsHandoff
      /writeSuccessWithdrawalsLoopSpec).
    iExists sp, pointer, base, (S remaining), (0%nat), remaining, bytes,
      ([] : list (bv 8)), bytes, tail.
    iEval (rewrite /writeSuccessWithdrawalsScratch).
    iFrame "Hsys Hother H2 H8 H9 H18 Hempty Hbytes HupperScratch HlowerScratch
      Hmmio Htrace HP Hinv Hexit".
Qed.
