Require Import ZesuSsz.Automation.All.
From Coq Require Import Lists.List ZArith.ZArith.
Require Import isla.riscv64.riscv64.
From IslaTraces.write_success_blocks Require Import Index.
Require Import ZesuSsz.Contracts.IslarisMachine.
Require Import ZesuSsz.Contracts.IslarisCode.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessEvents.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessByteLists.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessTransactionsSpec.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessTransactionsPost1566c.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessTransactionsPost1566cEvents.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessTransactionsPost15674Boundary.

Definition writeSuccessTransactionsPostAt15674EventsSpec
    `{!islaG Sigma} `{!threadG} (P : iProp Sigma) : iProp Sigma :=
  (∃ (sp : bv 64) (base : Z) (transactions : list writeSuccessTransaction)
      (bytes : list (bv 8)) (tail : spec) (first second : bv 64)
      (items : list ByteListItem),
    reg_col zesu_ram_sys_regs ∗ "x1" ↦ᵣ RVal_Bits (BV 64 0x15670) ∗
    reg_col writeSuccessTransactionsPostOtherRegShapes ∗
    "x2" ↦ᵣ RVal_Bits sp ∗ "x10" ↦ᵣ RVal_Bits first ∗
    "x11" ↦ᵣ RVal_Bits second ∗ base ↦ₘ∗ bytes ∗
    writeSuccessTransactionsOwn transactions ∗
    (bv_unsigned sp - 48) ↦ₘ? 152 ∗
    (bv_unsigned sp + 104) ↦ₘ Z_to_bv 64 base ∗
    (bv_unsigned sp + 112) ↦ₘ Z_to_bv 64 (Z.of_nat (length transactions)) ∗
    (bv_unsigned sp + 120) ↦ₘ? 984 ∗
    (bv_unsigned sp + 1104) ↦ₘ first ∗
    (bv_unsigned sp + 1112) ↦ₘ second ∗
    (bv_unsigned sp + 1120) ↦ₘ? 776 ∗
    byteListItemResources (bv_unsigned first) items ∗
    ⌜writeSuccessTransactionsPost15674ByteListFacts sp first second items⌝ ∗
    mmio_range 0x2401a0c0 16 ∗
    spec_trace (writeOutputEvents (sp - BV 64 48)%bv (BV 64 8)
      (byteListItemEvents (sp - BV 64 32)%bv items
        (writeOutputEvents (sp - BV 64 16)%bv (BV 64 8) tail))) ∗
    ((bv_unsigned sp - 80) ↦ₘ? 32 ∗
     ⌜bv_unsigned sp `mod` 16 = 0⌝ ∗ ⌜bv_unsigned sp `mod` 8 = 0⌝ ∗
     ⌜0x20000000 <= bv_unsigned sp - 48⌝ ∗
     ⌜bv_unsigned sp + 1896 < 0x40000000⌝ ∗ P) ∗ True)%I.

Global Instance : LithiumUnfold
    (@writeSuccessTransactionsPostAt15674EventsSpec) := I.

Lemma write_success_transactions_post_15670_events
    `{!islaG Sigma} `{!threadG} (P : iProp Sigma) :
  instr_lookup_resources IslaTraces.write_success_blocks.Index.lookup -∗
  instr_body 0x15674 (writeSuccessTransactionsPostAt15674EventsSpec P) -∗
  instr_body 0x15670 (writeSuccessTransactionsPostAt15670EventsSpec P).
Proof.
  move => *. iStartProof. iIntros "#Hlookup Hnext".
  liARun.
  all: destruct H0 as
    (HsecondLength & HitemsLength & HfirstAlign & HfirstLower & HfirstUpper &
     HspExtract & HspCallLower & HspMax).
  Unshelve. all: prepare_sidecond.
  all: try assumption.
  all: try bv_solve.
  all: try lia.
  all: try iFrame.
  Unshelve.
  all: try exact inhabitant.
  all: try bv_solve.
  Unshelve.
  all: iExists (items, tail, bytes, transactions, base, tt)ₗ.
  all: iRename select (mmio_range 0x2401a0c0 16)%I into "Hmmio".
  all: iFrame.
  all: repeat iSplit; try iPureIntro; try assumption; try lia.
  all: try iExact "Hmmio".
Qed.
