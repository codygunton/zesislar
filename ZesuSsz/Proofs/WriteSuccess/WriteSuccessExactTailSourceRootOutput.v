Require Import ZesuSsz.Automation.All.
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Contracts.IslarisMachine.
Require Import ZesuSsz.Export.Snapshots.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessPayloadCall.
Require Import ZesuSsz.Automation.ArraySlices.
From IslaTraces.write_success_100 Require Import instrs.
Import ZesuSsz.Automation.Calls.FramedContinuations.
Import ZesuSsz.Automation.ArraySlices.SliceMatching.

Definition exactSourceRootOtherRegisters : list string :=
  ["x3"; "x4"; "x6"; "x7"; "x8"; "x9"; "x12"; "x13"; "x14";
   "x15"; "x16"; "x17"; "x18"; "x19"; "x20"; "x21"; "x22";
   "x23"; "x24"; "x25"; "x26"; "x27"; "x28"; "x29"; "x30"; "x31"].
Definition exactSourceRootPost `{!islaG Sigma} `{!threadG}
    (sp : bv 64) (bytes : list (bv 8)) (tail : spec) (P : iProp Sigma) : iProp Sigma :=
  (reg_col zesu_ram_sys_regs ∗ "x2" ↦ᵣ RVal_Bits sp ∗
   reg_col ((fun r => (KindReg r, BitsShape 64)) <$>
     ("x1" :: "x5" :: "x10" :: "x11" :: exactSourceRootOtherRegisters)) ∗
   (bv_unsigned sp + 312) ↦ₘ∗ bytes ∗ mmio_range (machineOutputAddress defaultMap) 16 ∗
   spec_trace tail ∗ P ∗ True)%I.
Global Instance : LithiumUnfold (@exactSourceRootPost) := I.
Definition exactSourceRootEntry `{!islaG Sigma} `{!threadG}
    (sp oldra old5 olddata oldsize : bv 64) (bytes : list (bv 8)) (tail : spec) (P : iProp Sigma) : iProp Sigma :=
  (reg_col zesu_ram_sys_regs ∗ "x2" ↦ᵣ RVal_Bits sp ∗
   "x1" ↦ᵣ RVal_Bits oldra ∗ "x5" ↦ᵣ RVal_Bits old5 ∗
   "x10" ↦ᵣ RVal_Bits olddata ∗ "x11" ↦ᵣ RVal_Bits oldsize ∗
   reg_col ((fun r => (KindReg r, BitsShape 64)) <$> exactSourceRootOtherRegisters) ∗
   (bv_unsigned sp + 312) ↦ₘ∗ bytes ∗ mmio_range (machineOutputAddress defaultMap) 16 ∗
   spec_trace (writeOutputEvents (sp + BV 64 1000)%bv (BV 64 32)
     (take 32 (drop 688 bytes)) tail) ∗
   ⌜length bytes = 720%nat⌝ ∗ ⌜bv_unsigned sp `mod` 16 = 0⌝ ∗
   ⌜(mapRamBase defaultMap) <= bv_unsigned sp⌝ ∗ ⌜bv_unsigned sp + 1896 < (machineRamEnd defaultMap)⌝ ∗
   P ∗ instr_pre 0x1573c (exactSourceRootPost sp bytes tail P) ∗ True)%I.
Global Instance : LithiumUnfold (@exactSourceRootEntry) := I.
Lemma exact_source_root_output_correct `{!islaG Sigma} `{!threadG}
    sp oldra old5 olddata oldsize bytes tail (P : iProp Sigma) :
  ([∗ list] instruction ∈ IslaTraces.write_success_100.instrs.instr_map,
    instr instruction.1 (Some instruction.2))%I -∗
  □ instr_pre 0x10190 zesuWriteOutputPayloadCallSpec -∗
  instr_body 0x1572c (exactSourceRootEntry sp oldra old5 olddata oldsize bytes tail P).
Proof.
  zesu_block.
  all: have Hindex : IslarisMemory.array_region_start 8 (bv_unsigned sp + 312)
    (bv_unsigned (sp + BV 64 1000)%bv) = 688%nat.
  all: try (unfold IslarisMemory.array_region_start; cbn; rewrite Z.div_1_r;
    replace (bv_unsigned (sp + BV 64 1000)%bv - (bv_unsigned sp + 312))%Z
      with 688%Z by bv_solve; reflexivity).
  all: rewrite Hindex.
  all: try bv_solve.
  all: zesu_pack (tail, take 32 (drop 688 bytes), tt)ₗ.
  all: zesu_run.
  all: zesu_finish.
Qed.
Print Assumptions exact_source_root_output_correct.
