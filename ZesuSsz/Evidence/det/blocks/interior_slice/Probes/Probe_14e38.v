Require Import ZesuSsz.Automation.All.
Require Import ZesuSsz.Automation.SealedCoverage.
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessCalls.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessHeaderSpec.
Definition HeaderState_14e28
    `{!islaG Sigma} `{!threadG} (sp : bv 64) (bytes : list (bv 8)) (tail : spec) (P : iProp Sigma) : iProp Sigma :=
  ((reg_col zesu_ram_sys_regs) ∗
   (reg_col [(KindReg "x1", BitsShape 64); (KindReg "x3", BitsShape 64); (KindReg "x4", BitsShape 64); (KindReg "x8", BitsShape 64); (KindReg "x9", BitsShape 64); (KindReg "x10", BitsShape 64); (KindReg "x11", BitsShape 64); (KindReg "x12", BitsShape 64); (KindReg "x13", BitsShape 64); (KindReg "x14", BitsShape 64); (KindReg "x15", BitsShape 64); (KindReg "x16", BitsShape 64); (KindReg "x17", BitsShape 64); (KindReg "x18", BitsShape 64); (KindReg "x19", BitsShape 64); (KindReg "x20", BitsShape 64); (KindReg "x21", BitsShape 64); (KindReg "x22", BitsShape 64); (KindReg "x23", BitsShape 64); (KindReg "x24", BitsShape 64); (KindReg "x25", BitsShape 64); (KindReg "x26", BitsShape 64); (KindReg "x27", BitsShape 64)]) ∗
   ("x2" ↦ᵣ RVal_Bits sp) ∗
   ((bv_unsigned sp + 104) ↦ₘ? 16) ∗
   ((bv_unsigned sp + 312) ↦ₘ∗ bytes) ∗
   ((bv_unsigned sp + 1032) ↦ₘ∗ take 592 bytes) ∗
   ((bv_unsigned sp + 1624) ↦ₘ? 272) ∗
   (mmio_range (604086456 + 8) 16) ∗
   (spec_trace (writeSuccessHeaderEventsAfterTag sp tail)) ∗
   (P) ∗
   (instr_pre 85640 (writeSuccessHeaderPost sp bytes tail P)) ∗
   (reg_col ((fun register => (KindReg register, BitsShape 64)) <$> tmp_registers)) ∗
   (⌜True⌝) ∗
   (⌜bv_unsigned sp + 1896 < machineRamEnd defaultMap⌝) ∗
   (⌜mapRamBase defaultMap ≤ bv_unsigned sp⌝) ∗
   (⌜bv_unsigned sp `mod` 16 = 0⌝) ∗
   (⌜length bytes = 720%nat⌝) ∗
   True)%I.
Global Instance : LithiumUnfold (@HeaderState_14e28) := I.
Global Typeclasses Opaque HeaderState_14e28.

Definition HeaderState_14e38
    `{!islaG Sigma} `{!threadG} (sp : bv 64) (bytes : list (bv 8)) (tail : spec) (P : iProp Sigma) : iProp Sigma :=
  ((reg_col zesu_ram_sys_regs) ∗
   (reg_col [(KindReg "x1", BitsShape 64); (KindReg "x3", BitsShape 64); (KindReg "x4", BitsShape 64); (KindReg "x8", BitsShape 64); (KindReg "x9", BitsShape 64); (KindReg "x10", BitsShape 64); (KindReg "x11", BitsShape 64); (KindReg "x12", BitsShape 64); (KindReg "x13", BitsShape 64); (KindReg "x14", BitsShape 64); (KindReg "x15", BitsShape 64); (KindReg "x16", BitsShape 64); (KindReg "x17", BitsShape 64); (KindReg "x18", BitsShape 64); (KindReg "x19", BitsShape 64); (KindReg "x20", BitsShape 64); (KindReg "x21", BitsShape 64); (KindReg "x22", BitsShape 64); (KindReg "x23", BitsShape 64); (KindReg "x24", BitsShape 64); (KindReg "x25", BitsShape 64); (KindReg "x26", BitsShape 64); (KindReg "x27", BitsShape 64)]) ∗
   ("x2" ↦ᵣ RVal_Bits sp) ∗
   ((bv_unsigned sp + 104) ↦ₘ? 16) ∗
   ((bv_unsigned sp + 312) ↦ₘ∗ bytes) ∗
   ((bv_unsigned sp + 1032) ↦ₘ∗ take 592 bytes) ∗
   ((bv_unsigned sp + 1624) ↦ₘ? 272) ∗
   (mmio_range (604086456 + 8) 16) ∗
   (spec_trace (writeSuccessHeaderEventsAfter1184 sp tail)) ∗
   (P) ∗
   (instr_pre 85640 (writeSuccessHeaderPost sp bytes tail P)) ∗
   (reg_col ((fun register => (KindReg register, BitsShape 64)) <$> tmp_registers)) ∗
   (⌜True⌝) ∗
   (⌜bv_unsigned sp + 1896 < machineRamEnd defaultMap⌝) ∗
   (⌜mapRamBase defaultMap ≤ bv_unsigned sp⌝) ∗
   (⌜bv_unsigned sp `mod` 16 = 0⌝) ∗
   (⌜length bytes = 720%nat⌝) ∗
   True)%I.
Global Instance : LithiumUnfold (@HeaderState_14e38) := I.
Global Typeclasses Opaque HeaderState_14e38.

Definition HeaderState_14e48
    `{!islaG Sigma} `{!threadG} (sp : bv 64) (bytes : list (bv 8)) (tail : spec) (P : iProp Sigma) : iProp Sigma :=
  ((reg_col zesu_ram_sys_regs) ∗
   (reg_col [(KindReg "x1", BitsShape 64); (KindReg "x3", BitsShape 64); (KindReg "x4", BitsShape 64); (KindReg "x8", BitsShape 64); (KindReg "x9", BitsShape 64); (KindReg "x10", BitsShape 64); (KindReg "x11", BitsShape 64); (KindReg "x12", BitsShape 64); (KindReg "x13", BitsShape 64); (KindReg "x14", BitsShape 64); (KindReg "x15", BitsShape 64); (KindReg "x16", BitsShape 64); (KindReg "x17", BitsShape 64); (KindReg "x18", BitsShape 64); (KindReg "x19", BitsShape 64); (KindReg "x20", BitsShape 64); (KindReg "x21", BitsShape 64); (KindReg "x22", BitsShape 64); (KindReg "x23", BitsShape 64); (KindReg "x24", BitsShape 64); (KindReg "x25", BitsShape 64); (KindReg "x26", BitsShape 64); (KindReg "x27", BitsShape 64)]) ∗
   ("x2" ↦ᵣ RVal_Bits sp) ∗
   ((bv_unsigned sp + 104) ↦ₘ? 16) ∗
   ((bv_unsigned sp + 312) ↦ₘ∗ bytes) ∗
   ((bv_unsigned sp + 1032) ↦ₘ∗ take 592 bytes) ∗
   ((bv_unsigned sp + 1624) ↦ₘ? 272) ∗
   (mmio_range (604086456 + 8) 16) ∗
   (spec_trace (writeSuccessHeaderEventsAfter1216 sp tail)) ∗
   (P) ∗
   (instr_pre 85640 (writeSuccessHeaderPost sp bytes tail P)) ∗
   (reg_col ((fun register => (KindReg register, BitsShape 64)) <$> tmp_registers)) ∗
   (⌜True⌝) ∗
   (⌜bv_unsigned sp + 1896 < machineRamEnd defaultMap⌝) ∗
   (⌜mapRamBase defaultMap ≤ bv_unsigned sp⌝) ∗
   (⌜bv_unsigned sp `mod` 16 = 0⌝) ∗
   (⌜length bytes = 720%nat⌝) ∗
   True)%I.
Global Instance : LithiumUnfold (@HeaderState_14e48) := I.
Global Typeclasses Opaque HeaderState_14e48.

Definition HeaderState_14e58
    `{!islaG Sigma} `{!threadG} (sp : bv 64) (bytes : list (bv 8)) (tail : spec) (P : iProp Sigma) : iProp Sigma :=
  ((reg_col zesu_ram_sys_regs) ∗
   (reg_col [(KindReg "x1", BitsShape 64); (KindReg "x3", BitsShape 64); (KindReg "x4", BitsShape 64); (KindReg "x8", BitsShape 64); (KindReg "x9", BitsShape 64); (KindReg "x10", BitsShape 64); (KindReg "x11", BitsShape 64); (KindReg "x12", BitsShape 64); (KindReg "x13", BitsShape 64); (KindReg "x14", BitsShape 64); (KindReg "x15", BitsShape 64); (KindReg "x16", BitsShape 64); (KindReg "x17", BitsShape 64); (KindReg "x18", BitsShape 64); (KindReg "x19", BitsShape 64); (KindReg "x20", BitsShape 64); (KindReg "x21", BitsShape 64); (KindReg "x22", BitsShape 64); (KindReg "x23", BitsShape 64); (KindReg "x24", BitsShape 64); (KindReg "x25", BitsShape 64); (KindReg "x26", BitsShape 64); (KindReg "x27", BitsShape 64)]) ∗
   ("x2" ↦ᵣ RVal_Bits sp) ∗
   ((bv_unsigned sp + 104) ↦ₘ? 16) ∗
   ((bv_unsigned sp + 312) ↦ₘ∗ bytes) ∗
   ((bv_unsigned sp + 1032) ↦ₘ∗ take 592 bytes) ∗
   ((bv_unsigned sp + 1624) ↦ₘ? 272) ∗
   (mmio_range (604086456 + 8) 16) ∗
   (spec_trace (writeSuccessHeaderEventsAfter1236 sp tail)) ∗
   (P) ∗
   (instr_pre 85640 (writeSuccessHeaderPost sp bytes tail P)) ∗
   (reg_col ((fun register => (KindReg register, BitsShape 64)) <$> tmp_registers)) ∗
   (⌜True⌝) ∗
   (⌜bv_unsigned sp + 1896 < machineRamEnd defaultMap⌝) ∗
   (⌜mapRamBase defaultMap ≤ bv_unsigned sp⌝) ∗
   (⌜bv_unsigned sp `mod` 16 = 0⌝) ∗
   (⌜length bytes = 720%nat⌝) ∗
   True)%I.
Global Instance : LithiumUnfold (@HeaderState_14e58) := I.
Global Typeclasses Opaque HeaderState_14e58.

Definition HeaderState_14e68
    `{!islaG Sigma} `{!threadG} (sp : bv 64) (bytes : list (bv 8)) (tail : spec) (P : iProp Sigma) : iProp Sigma :=
  ((reg_col zesu_ram_sys_regs) ∗
   (reg_col [(KindReg "x1", BitsShape 64); (KindReg "x3", BitsShape 64); (KindReg "x4", BitsShape 64); (KindReg "x8", BitsShape 64); (KindReg "x9", BitsShape 64); (KindReg "x10", BitsShape 64); (KindReg "x11", BitsShape 64); (KindReg "x12", BitsShape 64); (KindReg "x13", BitsShape 64); (KindReg "x14", BitsShape 64); (KindReg "x15", BitsShape 64); (KindReg "x16", BitsShape 64); (KindReg "x17", BitsShape 64); (KindReg "x18", BitsShape 64); (KindReg "x19", BitsShape 64); (KindReg "x20", BitsShape 64); (KindReg "x21", BitsShape 64); (KindReg "x22", BitsShape 64); (KindReg "x23", BitsShape 64); (KindReg "x24", BitsShape 64); (KindReg "x25", BitsShape 64); (KindReg "x26", BitsShape 64); (KindReg "x27", BitsShape 64)]) ∗
   ("x2" ↦ᵣ RVal_Bits sp) ∗
   ((bv_unsigned sp + 104) ↦ₘ? 16) ∗
   ((bv_unsigned sp + 312) ↦ₘ∗ bytes) ∗
   ((bv_unsigned sp + 1032) ↦ₘ∗ take 592 bytes) ∗
   ((bv_unsigned sp + 1624) ↦ₘ? 272) ∗
   (mmio_range (604086456 + 8) 16) ∗
   (spec_trace (writeSuccessHeaderEventsAfter1268 sp tail)) ∗
   (P) ∗
   (instr_pre 85640 (writeSuccessHeaderPost sp bytes tail P)) ∗
   (reg_col ((fun register => (KindReg register, BitsShape 64)) <$> tmp_registers)) ∗
   (⌜True⌝) ∗
   (⌜bv_unsigned sp + 1896 < machineRamEnd defaultMap⌝) ∗
   (⌜mapRamBase defaultMap ≤ bv_unsigned sp⌝) ∗
   (⌜bv_unsigned sp `mod` 16 = 0⌝) ∗
   (⌜length bytes = 720%nat⌝) ∗
   True)%I.
Global Instance : LithiumUnfold (@HeaderState_14e68) := I.
Global Typeclasses Opaque HeaderState_14e68.

Definition HeaderState_14e78
    `{!islaG Sigma} `{!threadG} (sp : bv 64) (bytes : list (bv 8)) (tail : spec) (P : iProp Sigma) : iProp Sigma :=
  ((reg_col zesu_ram_sys_regs) ∗
   (reg_col [(KindReg "x1", BitsShape 64); (KindReg "x3", BitsShape 64); (KindReg "x4", BitsShape 64); (KindReg "x8", BitsShape 64); (KindReg "x9", BitsShape 64); (KindReg "x10", BitsShape 64); (KindReg "x11", BitsShape 64); (KindReg "x12", BitsShape 64); (KindReg "x13", BitsShape 64); (KindReg "x14", BitsShape 64); (KindReg "x15", BitsShape 64); (KindReg "x16", BitsShape 64); (KindReg "x17", BitsShape 64); (KindReg "x18", BitsShape 64); (KindReg "x19", BitsShape 64); (KindReg "x20", BitsShape 64); (KindReg "x21", BitsShape 64); (KindReg "x22", BitsShape 64); (KindReg "x23", BitsShape 64); (KindReg "x24", BitsShape 64); (KindReg "x25", BitsShape 64); (KindReg "x26", BitsShape 64); (KindReg "x27", BitsShape 64)]) ∗
   ("x2" ↦ᵣ RVal_Bits sp) ∗
   ((bv_unsigned sp + 104) ↦ₘ? 16) ∗
   ((bv_unsigned sp + 312) ↦ₘ∗ bytes) ∗
   ((bv_unsigned sp + 1032) ↦ₘ∗ take 592 bytes) ∗
   ((bv_unsigned sp + 1624) ↦ₘ? 272) ∗
   (mmio_range (604086456 + 8) 16) ∗
   (spec_trace (writeSuccessHeaderEventsAfter1300 sp tail)) ∗
   (P) ∗
   (reg_col ((fun register => (KindReg register, BitsShape 64)) <$> tmp_registers)) ∗
   (⌜True⌝) ∗
   (⌜bv_unsigned sp + 1896 < machineRamEnd defaultMap⌝) ∗
   (⌜mapRamBase defaultMap ≤ bv_unsigned sp⌝) ∗
   (⌜bv_unsigned sp `mod` 16 = 0⌝) ∗
   (⌜length bytes = 720%nat⌝) ∗
   True)%I.
Global Instance : LithiumUnfold (@HeaderState_14e78) := I.
Global Typeclasses Opaque HeaderState_14e78.

(* Generated by tools/det/gen_segment.py. Do not edit.

   0x14e38 to 0x14e48. Both boundary predicates
   are inferred, and the proof is the block automation alone. *)

Require Import isla.riscv64.riscv64.
From IslaTraces.write_success_blocks Require Import Index.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteOutputContract.
Require Import ZesuSsz.Automation.Sets.call.

#[local] Instance : LithiumUnfold (@writeOutputContract) := I.
#[local] Typeclasses Opaque writeOutputContract.

Lemma header_probe_14e38
    `{!islaG Sigma} `{!threadG} (sp : bv 64) (bytes : list (bv 8)) (tail : spec) (P : iProp Sigma) :
  instr_lookup_resources IslaTraces.write_success_blocks.Index.lookup -∗
  IslaTraces.write_success_blocks.Index.spec_instr_resources -∗
  □ instr_pre 0x10190 writeOutputContract -∗
  instr_pre 0x14e48
    (HeaderState_14e48 sp bytes tail P) -∗
  instr_body 0x14e38
    (HeaderState_14e38 sp bytes tail P).
Proof. zesu_block. Qed.
Print Assumptions header_probe_14e38.


