Require Import ZesuSsz.Automation.All.
Require Import ZesuMachineMap.Machine.
Require Import ZesuSsz.Automation.Calls.
Import FramedContinuations.
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Contracts.IslarisMachine.
Require Import ZesuSsz.Contracts.IslarisMemory.
Require Import ZesuSsz.Export.Snapshots.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessOutputWhole.
From Coq Require Import Lists.List ZArith.ZArith.
From IslaTraces.write_success_55 Require Import instrs.

Definition accessListsWholeOutputFrame `{!islaG Sigma} `{!threadG}
    (sp : bv 64) (bytes : list (bv 8)) (P : iProp Sigma) : iProp Sigma :=
  ("x2" ↦ᵣ RVal_Bits sp ∗
   P ∗ True)%I.
Global Instance : LithiumUnfold (@accessListsWholeOutputFrame) := I.

Definition accessListsWholeOutputEntry `{!islaG Sigma} `{!threadG}
    (sp old_ra old5 old_data old_size : bv 64) (bytes : list (bv 8))
    (tail : spec) (P : iProp Sigma) : iProp Sigma :=
  (reg_col zesu_ram_sys_regs ∗ "x2" ↦ᵣ RVal_Bits sp ∗
   "x1" ↦ᵣ RVal_Bits old_ra ∗ "x5" ↦ᵣ RVal_Bits old5 ∗
   "x10" ↦ᵣ RVal_Bits old_data ∗ "x11" ↦ᵣ RVal_Bits old_size ∗
   bv_unsigned (sp + BV 64 1744)%bv ↦ₘ∗ bytes ∗ mmio_range (machineOutputAddress defaultMap) 16 ∗
   spec_trace (writeOutputEvents (sp + BV 64 1760)%bv (BV 64 20)
     (take 20 (drop 16 bytes)) tail) ∗ ⌜length bytes = 40%nat⌝ ∗
   ⌜(mapRamBase defaultMap) <= bv_unsigned sp⌝ ∗
   ⌜bv_unsigned sp + 1784 < (machineRamEnd defaultMap)⌝ ∗ P ∗ True)%I.
Global Instance : LithiumUnfold (@accessListsWholeOutputEntry) := I.

Definition accessListsWholeOutputPost `{!islaG Sigma} `{!threadG}
    (sp : bv 64) (bytes : list (bv 8)) (tail : spec) (P : iProp Sigma) : iProp Sigma :=
  (reg_col zesu_ram_sys_regs ∗ "x1" ↦ᵣ RVal_Bits (BV 64 0x15210) ∗
   "x5" ↦ᵣ RVal_Bits (BV 64 (mapIoContextAddress defaultMap)) ∗
   "x10" ↦ᵣ RVal_Bits (sp + BV 64 1760)%bv ∗ "x11" ↦ᵣ RVal_Bits (BV 64 20) ∗
   bv_unsigned (sp + BV 64 1744)%bv ↦ₘ∗ bytes ∗
   mmio_range (machineOutputAddress defaultMap) 16 ∗ spec_trace tail ∗
   accessListsWholeOutputFrame sp bytes P ∗ True)%I.
Global Instance : LithiumUnfold (@accessListsWholeOutputPost) := I.

Lemma access_lists_whole_output_correct `{!islaG Sigma} `{!threadG}
    sp old_ra old5 old_data old_size bytes tail (P : iProp Sigma) :
  ([∗ list] instruction ∈ IslaTraces.write_success_55.instrs.instr_map,
    instr instruction.1 (Some instruction.2))%I -∗
  ([∗ list] instruction ∈ IslaTraces.write_success_01.instrs.instr_map,
    instr instruction.1 (Some instruction.2))%I -∗
  instr_body 0x15210 (accessListsWholeOutputPost sp bytes tail P) -∗
  instr_body 0x15200 (accessListsWholeOutputEntry sp old_ra old5 old_data old_size bytes tail P).
Proof.
  iStartProof. iIntros "#Hcaller #Houtput Hnext".
  iPoseProof (write_output_whole_correct (sp + BV 64 1760)%bv (BV 64 20)
    (BV 64 0x15210) (bv_unsigned (sp + BV 64 1744)%bv) 16 20 bytes tail
    (accessListsWholeOutputFrame sp bytes P) with "Houtput") as "Hcallee".
  iEval (rewrite /IslaTraces.write_success_55.instrs.instr_map /=) in "Hcaller".
  iDestruct "Hcaller" as "#(H0 & H1 & H2 & H3 & _)".
  zesu_run.
  Unshelve. all: prepare_sidecond.
  all: try assumption; try bv_solve; try lia.
Qed.
Print Assumptions access_lists_whole_output_correct.
