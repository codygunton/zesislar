From Coq Require Import Lists.List ZArith.ZArith.
Require Import isla.riscv64.riscv64.
From IslaTraces.write_success_blocks Require Import Index.
Require Import ZesuSsz.Contracts.IslarisMachine.
Require Import ZesuSsz.Contracts.IslarisCode.
Require Import ZesuSsz.Experiments.WriteSuccessTransactionsSpec.
Require Import ZesuSsz.Experiments.WriteSuccessTransactionsPost1566c.

Definition writeSuccessTransactionsPostAt15674Spec
    `{!islaG Sigma} `{!threadG} (P : iProp Sigma) : iProp Sigma :=
  (∃ (sp : bv 64) (base : Z) (transactions : list writeSuccessTransaction)
      (bytes : list (bv 8)) (tail : spec) (first second : bv 64),
    reg_col zesu_ram_sys_regs ∗
    "x1" ↦ᵣ RVal_Bits (BV 64 0x15670) ∗
    reg_col writeSuccessTransactionsPostOtherRegShapes ∗
    "x2" ↦ᵣ RVal_Bits sp ∗
    "x10" ↦ᵣ RVal_Bits first ∗
    "x11" ↦ᵣ RVal_Bits second ∗
    base ↦ₘ∗ bytes ∗
    writeSuccessTransactionsOwn transactions ∗
    writeSuccessTransactionsPostScratch15670 sp base (length transactions)
      first second ∗
    mmio_range 0x2401a0c0 16 ∗ spec_trace tail ∗
    ((bv_unsigned sp) ↦ₘ? 104 ∗
     (bv_unsigned sp + 1896) ↦ₘ? 104 ∗
     ⌜bv_unsigned sp `mod` 16 = 0⌝ ∗
     ⌜bv_unsigned sp `mod` 8 = 0⌝ ∗
     ⌜0x20000000 <= bv_unsigned sp - 48⌝ ∗
     ⌜bv_unsigned sp + 1896 < 0x40000000⌝ ∗ P) ∗ True)%I.

Global Instance : LithiumUnfold
    (@writeSuccessTransactionsPostAt15674Spec) := I.

Lemma write_success_transactions_post_15670_auipc
    `{!islaG Sigma} `{!threadG} (P : iProp Sigma) :
  instr_lookup_resources IslaTraces.write_success_blocks.Index.lookup -∗
  instr_body 0x15674 (writeSuccessTransactionsPostAt15674Spec P) -∗
  instr_body 0x15670 (writeSuccessTransactionsPostAt15670Spec P).
Proof.
  move => *.
  iStartProof.
  iIntros "#Hlookup Hnext".
  liARun.
  Unshelve. all: prepare_sidecond.
  all: try assumption.
  all: try bv_solve.
  all: try lia.
  all: try iFrame.
  Unshelve.
  all: try exact inhabitant.
  all: try bv_solve.
  Unshelve.
  all: iExists (tail, bytes, transactions, base, tt)ₗ.
  all: iRename select (mmio_range 0x2401a0c0 16)%I into "Hmmio".
  all: iFrame.
  all: iSplit; [iExact "Hmmio"|].
  all: repeat iSplit; try iPureIntro; try assumption; try lia.
Qed.
