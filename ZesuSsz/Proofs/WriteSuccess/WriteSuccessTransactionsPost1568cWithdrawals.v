From Coq Require Import ZArith.ZArith.
Require Import isla.riscv64.riscv64.
From IslaTraces.write_success_blocks Require Import Index.
Require Import ZesuSsz.Contracts.IslarisCode.
Require Import ZesuSsz.Contracts.IslarisMachine.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessTransactionsPost1568c.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessTransactionsPost15690Withdrawals.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessTransactionsPostWithdrawalsHandoff.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessWithdrawalsSpec.

Definition writeSuccessTransactionsPost1568cWithdrawalsRest
    `{!islaG Sigma} `{!threadG} (sp : bv 64) (P : iProp Sigma) : iProp Sigma :=
  (∃ (pointer : bv 64) (base : Z) (total processed remaining : nat)
      (bytes prefix suffix : list (bv 8)) (tail : spec),
    reg_col writeSuccessWithdrawalsOtherRegShapes ∗
    "x8" ↦ᵣ RVal_Bits pointer ∗
    "x9" ↦ᵣ RVal_Bits (Z_to_bv 64 (Z.of_nat (S remaining))) ∗
    base ↦ₘ∗ prefix ∗ bv_unsigned pointer ↦ₘ∗ suffix ∗
    writeSuccessWithdrawalsScratch sp ∗ mmio_range 0x2401a0c0 16 ∗
    spec_trace (writeSuccessWithdrawalsEvents sp (S remaining) tail) ∗ P ∗
    writeSuccessWithdrawalsInvariant sp pointer base total processed remaining
      bytes prefix suffix ∗
    instr_pre 0x156e8
      (writeSuccessWithdrawalsLoopExit sp base total bytes tail P) ∗ True)%I.

Definition writeSuccessTransactionsPost1568cWithdrawalsSpec
    `{!islaG Sigma} `{!threadG} (P : iProp Sigma) : iProp Sigma :=
  (∃ (sp : bv 64),
    reg_col zesu_ram_sys_regs ∗ "x2" ↦ᵣ RVal_Bits sp ∗
    "x18" ↦ᵣ: (fun _ => True) ∗
    writeSuccessTransactionsPost1568cWithdrawalsRest sp P)%I.

Global Instance : LithiumUnfold
    (@writeSuccessTransactionsPost1568cWithdrawalsRest) := I.
Global Instance : LithiumUnfold
    (@writeSuccessTransactionsPost1568cWithdrawalsSpec) := I.

Lemma write_success_transactions_post_1568c_withdrawals
    `{!islaG Sigma} `{!threadG} (P : iProp Sigma) :
  instr_lookup_resources IslaTraces.write_success_blocks.Index.lookup -∗
  □ instr_pre 0x15694 (writeSuccessTransactionsPostWithdrawalsHandoff P) -∗
  instr_body 0x1568c (writeSuccessTransactionsPost1568cWithdrawalsSpec P).
Proof.
  iStartProof. iIntros "#Hlookup #Hloop".
  rewrite instr_pre'_eq. iIntros "Hentry".
  iEval (rewrite /writeSuccessTransactionsPost1568cWithdrawalsSpec) in "Hentry".
  iDestruct "Hentry" as (sp) "(Hsys & H2 & H18 & Hrest)".
  iEval (rewrite -instr_pre'_eq) in "Hloop".
  iPoseProof (write_success_transactions_post_15690_withdrawals P with
    "Hlookup Hloop") as "Hadapter".
  iAssert (instr_body 0x15690
    (reg_col zesu_ram_sys_regs ∗ "x2" ↦ᵣ RVal_Bits sp ∗
     "x18" ↦ᵣ RVal_Bits (sp + BV 64 1768)%bv ∗
     writeSuccessTransactionsPost1568cWithdrawalsRest sp P))%I
    with "[Hadapter]" as "Hnext".
  { iApply (instr_pre_wand 0x15690 0x15690 false false with "Hadapter");
      [done | done |].
    iIntros "Hpost".
    iDestruct "Hpost" as "(Hsys & H2 & H18 & Hrest)".
    iEval (rewrite /writeSuccessTransactionsPost1568cWithdrawalsRest) in "Hrest".
    iDestruct "Hrest" as
      (pointer base total processed remaining bytes prefix suffix tail)
      "(Hother & H8 & H9 & Hprefix & Hsuffix & Hscratch & Hmmio & Htrace &
        HP & Hinv & Hexit & _)".
    iEval (rewrite /writeSuccessTransactionsPostWithdrawalsHandoff
      /writeSuccessWithdrawalsLoopSpec).
    iExists sp, pointer, base, total, processed, remaining, bytes, prefix,
      suffix, tail.
    iFrame "Hsys Hother H2 H8 H9 H18 Hprefix Hsuffix Hscratch Hmmio Htrace HP
      Hinv Hexit".
  }
  iPoseProof (write_success_transactions_post_1568c_addi sp
    (writeSuccessTransactionsPost1568cWithdrawalsRest sp P) with
    "Hlookup Hnext") as "Haddi".
  iEval (rewrite instr_pre'_eq) in "Haddi".
  iDestruct ("Haddi" with "[Hsys H2 H18 Hrest]") as (ins) "(Hinstr & Hwp)".
  { iFrame "Hsys H2 H18 Hrest". }
  iExists ins. iFrame "Hinstr". iExact "Hwp".
Qed.
