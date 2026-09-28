Require Import ZesuSsz.Automation.All.
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Contracts.IslarisMemory.
Require Import ZesuSsz.Automation.Sets.v2.
Require Import ZesuSsz.Automation.ArrayLoadPriority.
From IslaTraces.write_success_blocks Require Import Index.
From Coq Require Import Lists.List.
Import ListNotations.
Open Scope Z_scope.

(* This is the suffix array left by the first descriptor load in TF1.
   The next instruction loads the size word at sp+928. *)
Lemma test_region_suffix_priority_inactive `{!islaG Sigma} `{!threadG}
    (sp data size : bv 64) :
  instr_lookup_resources Index.lookup -∗
  instr_body_lookup_resources Index.body_lookup -∗
  "x2" ↦ᵣ RVal_Bits sp -∗
  (bv_unsigned sp + 920 + 8 *
     (array_region_start 64 (bv_unsigned sp + 920) (bv_unsigned sp + 920) + 1)%nat)
  ↦ₘ∗ drop
    (array_region_start 64 (bv_unsigned sp + 920) (bv_unsigned sp + 920) + 1)
    [data; size] -∗
  find_in_context (FindInstrKind 0x158e4 false)
    (fun ik => ⌜ik = IKPre false (zesu_ld_spec 0x158e4 "x11" "x2" 928)⌝ ∗ True).
Proof.
  iIntros "#Hcode #Htable Hreg Hsuffix".
  tryif zesu_array_load_priority then fail 1 "inactive switch selected a raw load" else idtac.
  liAStep. liShow. iSplit; [done | done].
Qed.
Print Assumptions test_region_suffix_priority_inactive.

Require Import ZesuSsz.Automation.Switches.ArrayLoadPriority.

Lemma test_region_suffix_priority `{!islaG Sigma} `{!threadG}
    (sp data size : bv 64) :
  instr_lookup_resources Index.lookup -∗
  instr_body_lookup_resources Index.body_lookup -∗
  "x2" ↦ᵣ RVal_Bits sp -∗
  (bv_unsigned sp + 920 + 8 *
     (array_region_start 64 (bv_unsigned sp + 920) (bv_unsigned sp + 920) + 1)%nat)
  ↦ₘ∗ drop
    (array_region_start 64 (bv_unsigned sp + 920) (bv_unsigned sp + 920) + 1)
    [data; size] -∗
  find_in_context (FindInstrKind 0x158e4 false)
    (fun ik => ⌜ik = IKInstr (Index.lookup 0x158e4)⌝ ∗ True).
Proof.
  iIntros "#Hcode #Htable Hreg Hsuffix".
  zesu_array_load_priority.
  iSplit; [done | done].
Qed.
Print Assumptions test_region_suffix_priority.
