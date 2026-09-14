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
From IslaTraces.write_success_93 Require Import instrs.
Local Remove Hints IslaTraces.write_success_93.a156cc_spec.a156cc_spec_inst : typeclass_instances.

Definition withdrawalWholeOutputFrame `{!islaG Sigma} `{!threadG}
    (sp : bv 64) (bytes : list (bv 8)) (P : iProp Sigma) : iProp Sigma :=
  ("x2" ↦ᵣ RVal_Bits sp ∗ "x18" ↦ᵣ RVal_Bits (sp + BV 64 1768)%bv ∗
   P ∗ True)%I.
Global Instance : LithiumUnfold (@withdrawalWholeOutputFrame) := I.

Definition withdrawalWholeOutputEntry `{!islaG Sigma} `{!threadG}
    (sp old_ra old5 old_data old_size : bv 64) (bytes : list (bv 8))
    (tail : spec) (P : iProp Sigma) : iProp Sigma :=
  (reg_col zesu_ram_sys_regs ∗ "x2" ↦ᵣ RVal_Bits sp ∗
   "x18" ↦ᵣ RVal_Bits (sp + BV 64 1768)%bv ∗ "x1" ↦ᵣ RVal_Bits old_ra ∗ "x5" ↦ᵣ RVal_Bits old5 ∗
   "x10" ↦ᵣ RVal_Bits old_data ∗ "x11" ↦ᵣ RVal_Bits old_size ∗
   bv_unsigned (sp + BV 64 1744)%bv ↦ₘ∗ bytes ∗ mmio_range (machineOutputAddress defaultMap) 16 ∗
   spec_trace (writeOutputEvents (sp + BV 64 1768)%bv (BV 64 20)
     (take 20 (drop 24 bytes)) tail) ∗ ⌜length bytes = 48%nat⌝ ∗
   ⌜(mapRamBase defaultMap) <= bv_unsigned sp⌝ ∗
   ⌜bv_unsigned sp + 1896 < (machineRamEnd defaultMap)⌝ ∗ P ∗ True)%I.
Global Instance : LithiumUnfold (@withdrawalWholeOutputEntry) := I.

Definition withdrawalWholeOutputPost `{!islaG Sigma} `{!threadG}
    (sp : bv 64) (bytes : list (bv 8)) (tail : spec) (P : iProp Sigma) : iProp Sigma :=
  (reg_col zesu_ram_sys_regs ∗ "x1" ↦ᵣ RVal_Bits (BV 64 0x156d0) ∗
   "x5" ↦ᵣ RVal_Bits (BV 64 (mapIoContextAddress defaultMap)) ∗
   "x10" ↦ᵣ RVal_Bits (sp + BV 64 1768)%bv ∗ "x11" ↦ᵣ RVal_Bits (BV 64 20) ∗
   bv_unsigned (sp + BV 64 1744)%bv ↦ₘ∗ bytes ∗
   mmio_range (machineOutputAddress defaultMap) 16 ∗ spec_trace tail ∗
   withdrawalWholeOutputFrame sp bytes P ∗ True)%I.
Global Instance : LithiumUnfold (@withdrawalWholeOutputPost) := I.

Lemma withdrawal_whole_output_correct `{!islaG Sigma} `{!threadG}
    sp old_ra old5 old_data old_size bytes tail (P : iProp Sigma) :
  ([∗ list] instruction ∈ IslaTraces.write_success_93.instrs.instr_map,
    instr instruction.1 (Some instruction.2))%I -∗
  ([∗ list] instruction ∈ IslaTraces.write_success_01.instrs.instr_map,
    instr instruction.1 (Some instruction.2))%I -∗
  instr_body 0x156d0 (withdrawalWholeOutputPost sp bytes tail P) -∗
  instr_body 0x156c0 (withdrawalWholeOutputEntry sp old_ra old5 old_data old_size bytes tail P).
Proof.
  iStartProof. iIntros "#Hcaller #Houtput Hnext".
  iPoseProof (write_output_whole_correct (sp + BV 64 1768)%bv (BV 64 20)
    (BV 64 0x156d0) (bv_unsigned (sp + BV 64 1744)%bv) 24 20 bytes tail
    (withdrawalWholeOutputFrame sp bytes P) with "Houtput") as "Hcallee".
  iEval (rewrite /IslaTraces.write_success_93.instrs.instr_map /=) in "Hcaller".
  iDestruct "Hcaller" as "#(H0 & H1 & H2 & H3 & _)".
  zesu_run.
  Unshelve. all: prepare_sidecond.
  all: try assumption; try bv_solve; try lia.
Qed.
Print Assumptions withdrawal_whole_output_correct.
