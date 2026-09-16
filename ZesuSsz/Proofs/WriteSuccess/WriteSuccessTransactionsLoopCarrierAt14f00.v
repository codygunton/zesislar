Require Import ZesuSsz.Automation.AllLegacy.
Require Import ZesuMachineMap.Machine.
From Coq Require Import Lists.List ZArith.ZArith.
Require Import isla.riscv64.riscv64.
From IslaTraces.write_success_blocks Require Import Index HintsTransactionsLoop.
Require Import ZesuSsz.Contracts.IslarisCode.
Require Import ZesuSsz.Contracts.IslarisMachine.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessByteLists.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessEvents.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessTransactionsLoopExitEvents.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessTransactionsPuncturedScratch.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessTransactionsSpec.

Definition writeSuccessTransactionsLoopCarrierAt14f00Spec
    `{!islaG Sigma} `{!threadG} (P : iProp Sigma) : iProp Sigma :=
  (∃ (sp : bv 64) (base : Z)
      (transactions processed remaining : list writeSuccessTransaction)
      (bytes prefix suffix : list (bv 8)) (tail : spec)
      (first second third fourth : bv 64) (items : list ByteListItem),
    reg_col zesu_ram_sys_regs ∗
    reg_col writeSuccessTransactionsOtherRegShapes ∗
    "x2" ↦ᵣ RVal_Bits sp ∗ "x10" ↦ᵣ: (fun _ => True) ∗
    "x11" ↦ᵣ RVal_Bits (Z_to_bv 64 (Z.of_nat (length processed))) ∗
    base ↦ₘ∗ prefix ∗
    (base + 288 * Z.of_nat (length processed)) ↦ₘ∗ suffix ∗
    writeSuccessTransactionsOwn processed ∗
    writeSuccessTransactionsOwn remaining ∗
    writeSuccessTransactionsPuncturedScratch sp base (length transactions) ∗
    writeSuccessTransactionsLoopCarrierPayload sp first second third fourth items ∗
    (bv_unsigned sp + 1744) ↦ₘ? 48 ∗ mmio_range (machineOutputAddress defaultMap) 16 ∗
    spec_trace (writeSuccessTransactionsEvents sp remaining
      (writeOutputEventsAny (sp - BV 64 48)%bv (BV 64 8)
        (byteListItemEvents (sp - BV 64 32)%bv items
          (writeOutputEventsAny (sp - BV 64 16)%bv (BV 64 8) tail)))) ∗ P ∗
    writeSuccessTransactionsInvariant sp base transactions processed remaining
      bytes prefix suffix ∗
    instr_pre writeSuccessTransactionsLoopExitAddress
      (writeSuccessTransactionsLoopCarrierExit P sp base transactions bytes tail
        first second third fourth items) ∗ True)%I.

Global Instance : LithiumUnfold
    (@writeSuccessTransactionsLoopCarrierAt14f00Spec) := I.

Lemma write_success_transactions_loop_carrier_14f00_load
    `{!islaG Sigma} `{!threadG} (P : iProp Sigma) :
  instr_lookup_resources IslaTraces.write_success_blocks.Index.lookup -∗
  instr_pre 0x14f04 (writeSuccessTransactionsLoopCarrierSpec P) -∗
  instr_body 0x14f00 (writeSuccessTransactionsLoopCarrierAt14f00Spec P).
Proof.
  iStartProof. iIntros "#Hlookup Hnext".
  liARun.
  Unshelve. all: prepare_sidecond.
  all: try assumption.
  all: try bv_solve.
  all: try lia.
  all: try iFrame.
  Unshelve. all: try exact inhabitant.
  Unshelve.
  iExists (items, fourth, third, second, first, tail,
    writeSuccessTransactionsBytes remaining,
    writeSuccessTransactionsBytes processed,
    writeSuccessTransactionsBytes (processed ++ remaining), remaining,
    processed, processed ++ remaining, base, sp, tt)ₗ.
  zesu_unfold_bv_bindings.
  iRename select ("x10" ↦ᵣ RVal_Bits
    (Z_to_bv 64 (Z.of_nat (length (processed ++ remaining)))))%I into "H10Loaded".
  iRename select (bv_unsigned (sp + BV 64 112)%bv ↦ₘ _)%I into "HtotalLoaded".
  zesu_normalize_memory_cell "HtotalLoaded" (bv_unsigned sp + 112).
  destruct H0 as
    (HsecondLength & HitemsLength & HfirstAlign & HfirstLower & HfirstUpper &
     HspExtract & HspCallLower & HspMax).
  rewrite /writeSuccessTransactionsLoopCarrierFrame
    /writeSuccessTransactionsPuncturedScratch
    /writeSuccessTransactionsLoopCarrierPayload
    /writeSuccessTransactionsWordsCarrier /writeSuccessTransactionsInvariant.
  cbn.
  iFrame.
  repeat iSplit; try iPureIntro; try assumption; try reflexivity; try bv_solve;
    try done.
Qed.

Print Assumptions write_success_transactions_loop_carrier_14f00_load.
