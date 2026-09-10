Require Import ZesuSsz.Automation.All.
From Coq Require Import Lists.List ZArith.ZArith.
Require Import isla.riscv64.riscv64.
From IslaTraces.write_success_117 Require Import a15970.
From IslaTraces.write_success_blocks Require Import Index.
Require Import ZesuSsz.Contracts.IslarisCode.
Require Import ZesuSsz.Contracts.IslarisMachine.

Definition writeSuccessSuffix15970ZeroSpec
    `{!islaG Sigma} `{!threadG} (P : iProp Sigma) : iProp Sigma :=
  (reg_col zesu_ram_sys_regs ∗ "x8" ↦ᵣ RVal_Bits (BV 64 0) ∗ P ∗
   instr_pre 0x15994
     (reg_col zesu_ram_sys_regs ∗ "x8" ↦ᵣ RVal_Bits (BV 64 0) ∗ P) ∗
   True)%I.

Global Instance : LithiumUnfold (@writeSuccessSuffix15970ZeroSpec) := I.

Definition writeSuccessSuffix15970NonzeroSpec
    `{!islaG Sigma} `{!threadG} (value : bv 64)
    (P : iProp Sigma) : iProp Sigma :=
  (reg_col zesu_ram_sys_regs ∗ "x8" ↦ᵣ RVal_Bits value ∗ P ∗
   instr_pre 0x15974
     (reg_col zesu_ram_sys_regs ∗ "x8" ↦ᵣ RVal_Bits value ∗ P) ∗
   True)%I.

Global Instance : LithiumUnfold (@writeSuccessSuffix15970NonzeroSpec) := I.

Definition writeSuccessSuffix15970BranchSpec
    `{!islaG Sigma} `{!threadG} (P : bv 64 -> iProp Sigma) : iProp Sigma :=
  (writeSuccessSuffix15970ZeroSpec (P (BV 64 0)) ∨
   ∃ value : bv 64, ⌜value <> BV 64 0⌝ ∗
     writeSuccessSuffix15970NonzeroSpec value (P value))%I.

Global Instance : LithiumUnfold (@writeSuccessSuffix15970BranchSpec) := I.

Lemma write_success_suffix_15970_branch
    `{!islaG Sigma} `{!threadG} (P : bv 64 -> iProp Sigma) :
  instr 0x15970 (Some a15970) -∗
  instr_body 0x15970 (writeSuccessSuffix15970BranchSpec P).
Proof.
  iStartProof. iIntros "#Hbranch".
  iApply (instr_pre_intro_Some with "Hbranch").
  iIntros "[Hzero | Hnonzero] HPC".
  - iEval (rewrite /writeSuccessSuffix15970ZeroSpec) in "Hzero".
    iDestruct "Hzero" as "(Hsys & H8 & HP & Hdest & _)".
    liARun.
    Unshelve. all: prepare_sidecond.
    all: try assumption; try bv_solve.
    Unshelve. all: try iFrame.
  - iDestruct "Hnonzero" as (value Hvalue) "Hnonzero".
    iEval (rewrite /writeSuccessSuffix15970NonzeroSpec) in "Hnonzero".
    iDestruct "Hnonzero" as "(Hsys & H8 & HP & Hdest & _)".
    liARun.
    Unshelve. all: prepare_sidecond.
    all: try assumption; try bv_solve.
    Unshelve. all: try iFrame.
    all: try (iExFalso; iPureIntro; apply Hvalue; bv_solve).
Qed.

Definition writeSuccessSuffix15970LoadedSpec
    `{!islaG Sigma} `{!threadG} (P : bv 64 -> iProp Sigma) : iProp Sigma :=
  (∃ (sp value : bv 64), reg_col zesu_ram_sys_regs ∗
    "x2" ↦ᵣ RVal_Bits sp ∗ "x8" ↦ᵣ RVal_Bits value ∗
    (bv_unsigned sp + 72) ↦ₘ value ∗ P value)%I.

Global Instance : LithiumUnfold (@writeSuccessSuffix15970LoadedSpec) := I.

Definition writeSuccessSuffix1596cLoadSpec
    `{!islaG Sigma} `{!threadG} (P : bv 64 -> iProp Sigma) : iProp Sigma :=
  (∃ (sp value : bv 64), reg_col zesu_ram_sys_regs ∗
    "x2" ↦ᵣ RVal_Bits sp ∗
    "x8" ↦ᵣ: (fun r => ⌜valu_has_shape r (BitsShape 64)⌝) ∗
    (bv_unsigned sp + 72) ↦ₘ value ∗ ⌜bv_unsigned sp `mod` 8 = 0⌝ ∗
    ⌜0x20000000 <= bv_unsigned sp + 72 < 0x40000000⌝ ∗
    instr_pre 0x15970 (writeSuccessSuffix15970LoadedSpec P) ∗
    P (bv_sign_extend 64 value))%I.

Global Instance : LithiumUnfold (@writeSuccessSuffix1596cLoadSpec) := I.

Lemma write_success_suffix_1596c_load
    `{!islaG Sigma} `{!threadG} (P : bv 64 -> iProp Sigma) :
  instr_lookup_resources IslaTraces.write_success_blocks.Index.lookup -∗
  instr_body 0x1596c (writeSuccessSuffix1596cLoadSpec P).
Proof.
  move => *. iStartProof. iIntros "_ #Hlookup". liARun.
  Unshelve. all: prepare_sidecond.
  all: try assumption; try unLET; try rewrite bv_sign_extend_64_idemp;
    try bv_solve; try lia.
  Unshelve. all: iFrame.
  all: lazymatch goal with |- ?G => fail "1596c load residual" G end.
Qed.
