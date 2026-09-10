Require Import ZesuSsz.Automation.All.
From Coq Require Import Lists.List.
Require Import isla.riscv64.riscv64.
From IslaTraces.write_success_00 Require Import instrs.
From IslaTraces.write_success_01 Require Import instrs.
From IslaTraces.write_success_02 Require Import instrs.
From IslaTraces.write_success_03 Require Import instrs.
From IslaTraces.write_success_04 Require Import instrs.
From IslaTraces.write_success_05 Require Import instrs.
From IslaTraces.write_success_06 Require Import instrs.
From IslaTraces.write_success_07 Require Import instrs.
From IslaTraces.write_success_08 Require Import instrs.
From IslaTraces.write_success_127 Require Import instrs.
From IslaTraces.write_success_blocks Require Import Index.
Require Import ZesuSsz.Contracts.IslarisCode.

(** All executable code used by the native [writeSuccess] proof. *)
Definition writeSuccessCompleteNativeCode `{!islaG Sigma} `{!threadG} :
    iProp Sigma :=
  (([∗ list] instruction ∈ IslaTraces.write_success_00.instrs.instr_map,
      instr instruction.1 (Some instruction.2)) ∗
   instr_lookup_resources IslaTraces.write_success_blocks.Index.lookup ∗
   IslaTraces.write_success_blocks.Index.spec_instr_resources ∗
   ([∗ list] instruction ∈ IslaTraces.write_success_01.instrs.instr_map,
      instr instruction.1 (Some instruction.2)) ∗
   ([∗ list] instruction ∈ IslaTraces.write_success_02.instrs.instr_map,
      instr instruction.1 (Some instruction.2)) ∗
   ([∗ list] instruction ∈ IslaTraces.write_success_03.instrs.instr_map,
      instr instruction.1 (Some instruction.2)) ∗
   ([∗ list] instruction ∈ IslaTraces.write_success_04.instrs.instr_map,
      instr instruction.1 (Some instruction.2)) ∗
   ([∗ list] instruction ∈ IslaTraces.write_success_05.instrs.instr_map,
      instr instruction.1 (Some instruction.2)) ∗
   ([∗ list] instruction ∈ IslaTraces.write_success_06.instrs.instr_map,
      instr instruction.1 (Some instruction.2)) ∗
   ([∗ list] instruction ∈ IslaTraces.write_success_07.instrs.instr_map,
      instr instruction.1 (Some instruction.2)) ∗
   ([∗ list] instruction ∈ IslaTraces.write_success_08.instrs.instr_map,
      instr instruction.1 (Some instruction.2)) ∗
   ([∗ list] instruction ∈ IslaTraces.write_success_127.instrs.instr_map,
      instr instruction.1 (Some instruction.2)))%I.

Global Instance : LithiumUnfold (@writeSuccessCompleteNativeCode) := I.

(** The main writer block resources from the complete native code bundle. *)
Definition writeSuccessNativeMainCode `{!islaG Sigma} `{!threadG} :
    iProp Sigma :=
  (instr_lookup_resources IslaTraces.write_success_blocks.Index.lookup ∗
   IslaTraces.write_success_blocks.Index.spec_instr_resources ∗ True)%I.

Lemma write_success_native_main_code `{!islaG Sigma} `{!threadG} :
  writeSuccessCompleteNativeCode -∗ writeSuccessNativeMainCode.
Proof.
  iIntros "#Hnative".
  rewrite /writeSuccessCompleteNativeCode /writeSuccessNativeMainCode.
  iDestruct "Hnative" as
    "(#Hprologue & #Hlookup & #Hmain & #Houtput & #Hmemcpy & #Hboolean &
      #Hoptional & #HbyteLists & #Hbytes & #Hint & #Hu256 & #Hint1645)".
  iFrame "Hlookup Hmain".
Qed.

Global Typeclasses Opaque writeSuccessNativeMainCode.
