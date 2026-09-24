Require Import ZesuSsz.Automation.AllLegacy.
From Coq Require Import Lists.List ZArith.ZArith.
Require Import isla.riscv64.riscv64.
From IslaTraces.write_success_blocks Require Import Index.
Require Import ZesuSsz.Contracts.IslarisCode.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessBitvector.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessNativeSuffixConditionalBranch.

Local Remove Hints subsume_instr_pre'_inst : typeclass_instances.
Local Remove Hints subsume_instr_pre_zesu_inst : typeclass_instances.
Local Existing Instance subsume_instr_pre_wand_inst | 1.

Definition writeSuccessSuffix15970Frame
    `{!islaG Sigma} `{!threadG} (P : bv 64 -> iProp Sigma)
    (value : bv 64) : iProp Sigma :=
  (∃ sp : bv 64,
    "x2" ↦ᵣ RVal_Bits sp ∗
    (bv_unsigned sp + 72) ↦ₘ value ∗ P value ∗ True)%I.

Global Instance : LithiumUnfold (@writeSuccessSuffix15970Frame) := I.

Lemma write_success_suffix_15970_loaded_branch
    `{!islaG Sigma} `{!threadG} (P : bv 64 -> iProp Sigma) :
  instr_lookup_resources IslaTraces.write_success_blocks.Index.lookup -∗
  instr_body 0x15974 (writeSuccessSuffix15970LoadedSpec P) -∗
  instr_body 0x15994 (writeSuccessSuffix15970LoadedSpec P) -∗
  instr_body 0x15970 (writeSuccessSuffix15970LoadedSpec P).
Proof. move => *. zesu_block. Qed.

Lemma write_success_suffix_1596c_load_branch
    `{!islaG Sigma} `{!threadG} (P : bv 64 -> iProp Sigma) :
  instr_lookup_resources IslaTraces.write_success_blocks.Index.lookup -∗
  instr_body 0x15974 (writeSuccessSuffix15970LoadedSpec P) -∗
  instr_body 0x15994 (writeSuccessSuffix15970LoadedSpec P) -∗
  instr_body 0x1596c (writeSuccessSuffix1596cLoadSpec P).
Proof. move => *. zesu_block. Qed.
