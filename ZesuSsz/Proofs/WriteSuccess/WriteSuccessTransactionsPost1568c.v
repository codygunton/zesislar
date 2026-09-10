Require Import ZesuSsz.Automation.All.
From Coq Require Import ZArith.ZArith.
Require Import isla.riscv64.riscv64.
From IslaTraces.write_success_blocks Require Import Index.
Require Import ZesuSsz.Contracts.IslarisMachine.
Require Import ZesuSsz.Contracts.IslarisCode.

Definition writeSuccessTransactionsPost1568cAddiSpec
    `{!islaG Sigma} `{!threadG} (pc : Z) : iProp Sigma :=
  (∃ sp : bv 64,
    reg_col zesu_ram_sys_regs ∗
    "x2" ↦ᵣ RVal_Bits sp ∗
    "x18" ↦ᵣ: (fun _ => True) ∗
    instr_pre (pc + 4)
      (reg_col zesu_ram_sys_regs ∗
       "x2" ↦ᵣ RVal_Bits sp ∗
       "x18" ↦ᵣ RVal_Bits (sp + BV 64 1768)%bv ∗ True))%I.

Global Instance : LithiumUnfold
    (@writeSuccessTransactionsPost1568cAddiSpec) := I.

Lemma write_success_transactions_post_1568c_addi_spec
    `{!islaG Sigma} `{!threadG} (pc : Z) :
  instr pc (Some IslaTraces.write_success_89.a1568c.a1568c) -∗
  instr_body pc (writeSuccessTransactionsPost1568cAddiSpec pc).
Proof.
  iStartProof.
  liARun.
  Unshelve. all: prepare_sidecond.
  all: bv_solve.
Qed.

Lemma write_success_transactions_post_1568c_addi
    `{!islaG Sigma} `{!threadG} (sp : bv 64) (P : iProp Sigma) :
  instr_lookup_resources IslaTraces.write_success_blocks.Index.lookup -∗
  instr_body 0x15690
    (reg_col zesu_ram_sys_regs ∗
     "x2" ↦ᵣ RVal_Bits sp ∗
     "x18" ↦ᵣ RVal_Bits (sp + BV 64 1768)%bv ∗ P) -∗
  instr_body 0x1568c
    (reg_col zesu_ram_sys_regs ∗
     "x2" ↦ᵣ RVal_Bits sp ∗
     "x18" ↦ᵣ: (fun _ => True) ∗ P).
Proof.
  iStartProof. iIntros "#Hlookup Hnext".
  iPoseProof "Hlookup" as "#Hlookup1568c".
  iEval (rewrite /instr_lookup_resources) in "Hlookup1568c".
  iPoseProof ("Hlookup1568c" $! 0x1568c with "[]") as "#Hinstr1568c".
  { iPureIntro.
    rewrite IslaTraces.write_success_blocks.Index.lookup_a1568c.
    done. }
  iEval (rewrite IslaTraces.write_success_blocks.Index.lookup_a1568c)
    in "Hinstr1568c".
  iPoseProof (write_success_transactions_post_1568c_addi_spec 0x1568c
    with "Hinstr1568c") as "Haddi".
  rewrite instr_pre'_eq. iIntros "Hentry".
  iDestruct "Hentry" as "(Hsys & H2 & H18 & HP)".
  iEval (rewrite /writeSuccessTransactionsPost1568cAddiSpec).
  iApply "Haddi".
  iExists sp.
  iFrame "Hsys H2 H18".
  rewrite instr_pre'_eq. iNext.
  iIntros "Hpost".
  iApply "Hnext".
  iDestruct "Hpost" as "(HsysPost & H2Post & H18Post & _)".
  iFrame.
Qed.
