Require Import ZesuSsz.Automation.All.
Require Import ZesuMachineMap.Machine.
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Contracts.IslarisMachine.
Require Import ZesuSsz.Export.Snapshots.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessOutput.
From Coq Require Import Lists.List.
From IslaTraces.write_success_46 Require Import instrs.
Local Existing Instance subsume_instr_pre_guard_inst | 0.

Definition transactionRecipientOutputEntry `{!islaG Sigma} `{!threadG}
    (sp old_ra old_x5 old_data old_size : bv 64) (payload : list (bv 8)) (tail : spec)
    (P : iProp Sigma) : iProp Sigma :=
  (reg_col zesu_ram_sys_regs ∗ "x2" ↦ᵣ RVal_Bits sp ∗ "x1" ↦ᵣ RVal_Bits old_ra ∗
   "x5" ↦ᵣ RVal_Bits old_x5 ∗ "x10" ↦ᵣ RVal_Bits old_data ∗
   "x11" ↦ᵣ RVal_Bits old_size ∗ bv_unsigned (sp + BV 64 1744)%bv ↦ₘ∗ payload ∗
   mmio_range (machineOutputAddress defaultMap) 16 ∗
   spec_trace (writeOutputEvents (sp + BV 64 1744)%bv (BV 64 20) payload tail) ∗ ⌜length payload = 20%nat⌝ ∗ P ∗ True)%I.
Global Instance : LithiumUnfold (@transactionRecipientOutputEntry) := I.

Definition transactionRecipientOutputPost `{!islaG Sigma} `{!threadG}
    (sp : bv 64) (payload : list (bv 8)) (tail : spec) (P : iProp Sigma) : iProp Sigma :=
  (reg_col zesu_ram_sys_regs ∗ "x1" ↦ᵣ RVal_Bits (BV 64 0x15190) ∗
   "x5" ↦ᵣ RVal_Bits (BV 64 (mapIoContextAddress defaultMap)) ∗ "x10" ↦ᵣ RVal_Bits (sp + BV 64 1744)%bv ∗
   "x11" ↦ᵣ RVal_Bits (BV 64 20) ∗ bv_unsigned (sp + BV 64 1744)%bv ↦ₘ∗ payload ∗
   mmio_range (machineOutputAddress defaultMap) 16 ∗ spec_trace tail ∗
   ("x2" ↦ᵣ RVal_Bits sp ∗ P ∗ True) ∗ True)%I.
Global Instance : LithiumUnfold (@transactionRecipientOutputPost) := I.

Lemma transactions_recipient_output_correct `{!islaG Sigma} `{!threadG}
    sp old_ra old_x5 old_data old_size payload tail (P : iProp Sigma) :
  ([∗ list] instruction ∈ IslaTraces.write_success_46.instrs.instr_map,
    instr instruction.1 (Some instruction.2))%I -∗
  □ instr_pre 0x10190 (writeOutputTraceSpec (sp + BV 64 1744)%bv (BV 64 20)
    (BV 64 0x15190) payload tail ("x2" ↦ᵣ RVal_Bits sp ∗ P ∗ True)) -∗
  instr_body 0x15190 (transactionRecipientOutputPost sp payload tail P) -∗
  instr_body 0x15180 (transactionRecipientOutputEntry sp old_ra old_x5 old_data old_size payload tail P).
Proof.
  zesu_block.
  all: try (eexists; eexists; repeat split; reflexivity).
  all: unfold transactionRecipientOutputPost; reflexivity.
Qed.
Print Assumptions transactions_recipient_output_correct.
Lemma transactions_recipient_output_call_correct `{!islaG Sigma} `{!threadG}
    sp oldra old5 olddata oldsize payload tail (P : iProp Sigma) :
  ([∗ list] instruction ∈ IslaTraces.write_success_46.instrs.instr_map,
    instr instruction.1 (Some instruction.2))%I -∗
  ([∗ list] instruction ∈ IslaTraces.write_success_01.instrs.instr_map,
    instr instruction.1 (Some instruction.2))%I -∗
  instr_body 0x15180
    (transactionRecipientOutputEntry sp oldra old5 olddata oldsize payload tail P ∗
     instr_pre 0x15190 (transactionRecipientOutputPost sp payload tail P) ∗ True).
Proof.
  iStartProof. iIntros "#Hcaller #Houtput".
  iAssert (□ instr_pre 0x10190
    (writeOutputTraceSpec (sp + BV 64 1744)%bv (BV 64 20) (BV 64 0x15190)
      payload tail ("x2" ↦ᵣ RVal_Bits sp ∗ P ∗ True)))%I as "#Hcallee".
  { iModIntro. iApply instr_pre_to_body. iNext.
    iApply write_output_trace_correct. iExact "Houtput". }
  iEval (rewrite /IslaTraces.write_success_46.instrs.instr_map /=) in "Hcaller".
  iDestruct "Hcaller" as "#(H0 & H1 & H2 & H3 & _)".
  zesu_run.
  all: try (eexists; eexists; repeat split; reflexivity).
  all: unfold transactionRecipientOutputPost; reflexivity.
Qed.
Print Assumptions transactions_recipient_output_call_correct.
