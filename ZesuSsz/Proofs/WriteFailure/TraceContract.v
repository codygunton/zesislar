Require Import ZesuSsz.Automation.All.
Require Import ZesuMachineMap.Machine.
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Contracts.Endpoints.
Require Import ZesuSsz.Generated.Level1.
From IslaTraces.write_failure Require Import instrs.
Require Import ZesuSsz.Proofs.WriteFailure.WriteFailure.
Require Import ZesuSsz.Export.Snapshots.

Definition writeFailureFramedPrefixInstrs : list (Z * isla_trace) :=
  [(0x161c0, a161c0); (0x161c4, a161c4); (0x161c8, a161c8);
   (0x161cc, a161cc); (0x161d0, a161d0)].

Definition writeFailureFramedTraceExit `{!islaG Sigma} `{!threadG}
    (tail : spec) (P : iProp Sigma) : iProp Sigma :=
  (reg_col zesu_sys_regs ∗
   "x1" ↦ᵣ RVal_Bits (BV 64 0x14d24) ∗
   "x5" ↦ᵣ RVal_Bits (BV 64 (mapIoContextAddress defaultMap)) ∗
   "x10" ↦ᵣ RVal_Bits (BV 64 0x177c8) ∗
   "x11" ↦ᵣ RVal_Bits (BV 64 6) ∗
   0x177c8 ↦ₘ∗ failureMemory ∗ mmio_range (machineOutputAddress defaultMap) 16 ∗
   spec_trace tail ∗ ("x6" ↦ᵣ RVal_Bits (BV 64 0x101cc) ∗ P ∗ True) ∗ True)%I.

Definition writeFailureFramedTraceEntry `{!islaG Sigma} `{!threadG}
    (tail : spec) (P : iProp Sigma) : iProp Sigma :=
  (∃ (old_x5 old_x6 old_x10 old_x11 : bv 64),
   reg_col zesu_sys_regs ∗
   "x1" ↦ᵣ RVal_Bits (BV 64 0x14d24) ∗
   "x5" ↦ᵣ RVal_Bits old_x5 ∗ "x6" ↦ᵣ RVal_Bits old_x6 ∗
   "x10" ↦ᵣ RVal_Bits old_x10 ∗ "x11" ↦ᵣ RVal_Bits old_x11 ∗
   0x177c8 ↦ₘ∗ failureMemory ∗ mmio_range (machineOutputAddress defaultMap) 16 ∗
   spec_trace (writeOutputEvents (BV 64 0x177c8) (BV 64 6) failureMemory tail) ∗
   P ∗ instr_pre 0x14d24 (writeFailureFramedTraceExit tail P) ∗ True)%I.
Global Instance : LithiumUnfold (@writeFailureFramedTraceEntry) := I.
Global Instance : LithiumUnfold (@writeFailureFramedTraceExit) := I.

Lemma write_failure_framed_prefix_correct `{!islaG Sigma} `{!threadG}
    (tail : spec) (P : iProp Sigma) :
  ([∗ list] i ∈ writeFailureFramedPrefixInstrs, instr i.1 (Some i.2)) -∗
  instr_body 0x10190
    (writeFailureOutputTraceSpec (BV 64 0x177c8) (BV 64 6) (BV 64 0x14d24)
      failureMemory tail ("x6" ↦ᵣ RVal_Bits (BV 64 0x101cc) ∗ P ∗ True)) -∗
  instr_body 0x161c0 (writeFailureFramedTraceEntry tail P).
Proof.
  unfold writeFailureFramedPrefixInstrs, writeFailureFramedTraceEntry, writeFailureFramedTraceExit, failureMemory.
  zesu_block.
Qed.
Print Assumptions write_failure_framed_prefix_correct.

Lemma write_failure_framed_trace_correct `{!islaG Sigma} `{!threadG}
    (tail : spec) (P : iProp Sigma) :
  ([∗ list] i ∈ writeFailureFramedPrefixInstrs, instr i.1 (Some i.2)) -∗
  ([∗ list] i ∈ skipn 5 IslaTraces.write_failure.instrs.instr_map,
    instr i.1 (Some i.2)) -∗
  instr_body 0x161c0 (writeFailureFramedTraceEntry tail P).
Proof.
  iIntros "Hprefix Houtput".
  iApply (write_failure_framed_prefix_correct tail P with "Hprefix").
  iApply (write_failure_output_trace_correct (BV 64 0x177c8) (BV 64 6) failureMemory tail ("x6" ↦ᵣ RVal_Bits (BV 64 0x101cc) ∗ P ∗ True)%I with "Houtput").
Qed.
Print Assumptions write_failure_framed_trace_correct.

Definition writeFailureTailResources `{!islaG Sigma} `{!threadG}
    (tail : spec) (P : iProp Sigma) :
    IslarisContractResources WriteFailureArgs ByteString := {|
  islarisCode :=
    (([∗ list] i ∈ writeFailureFramedPrefixInstrs, instr i.1 (Some i.2)) ∗
     ([∗ list] i ∈ skipn 5 IslaTraces.write_failure.instrs.instr_map,
       instr i.1 (Some i.2)))%I;
  islarisEntry := fun args =>
    (⌜failureReturnAddress args = 0x14d24⌝ ∗
     ∃ (old_x5 old_x6 old_x10 old_x11 : bv 64),
     reg_col zesu_sys_regs ∗
     "x1" ↦ᵣ RVal_Bits (BV 64 0x14d24) ∗
     "x5" ↦ᵣ RVal_Bits old_x5 ∗ "x6" ↦ᵣ RVal_Bits old_x6 ∗
     "x10" ↦ᵣ RVal_Bits old_x10 ∗ "x11" ↦ᵣ RVal_Bits old_x11 ∗
     0x177c8 ↦ₘ∗ failureMemory ∗ mmio_range (machineOutputAddress defaultMap) 16 ∗
     spec_trace (writeOutputEvents (BV 64 0x177c8) (BV 64 6) failureMemory tail) ∗
     P ∗ True)%I;
  islarisExit := fun _ bytes =>
    (⌜bytes = failureObservation⌝ ∗ writeFailureFramedTraceExit tail P)%I
|}.

Definition writeFailureTailModel (tail : spec) :
    IslarisContractModel WriteFailureArgs ByteString := {|
  islarisContractAllows := writeFailureAllows;
  islarisContractStep := fun _ _ => True;
  islarisContractResources := fun Sigma HG HT =>
    @writeFailureTailResources Sigma HG HT tail True%I
|}.

Theorem write_failure_tail_state_correct `{!islaG Sigma} `{!threadG}
    (tail : spec) (P : iProp Sigma) :
  ⊢ IslarisContractSpec 0x161c0 0x14d24
    writeFailureAllows (writeFailureTailResources tail P).
Proof.
  rewrite /IslarisContractSpec /writeFailureTailResources /=.
  iIntros "[Hprefix Houtput]" (args).
  iPoseProof (write_failure_framed_trace_correct tail P with "Hprefix Houtput") as "Hbody".
  rewrite instr_pre'_eq.
  iIntros "Hcontract".
  iApply "Hbody".
  rewrite /writeFailureFramedTraceEntry.
  iDestruct "Hcontract" as "[[%Hret Hentry] Hreturn]".
  iDestruct "Hentry" as (x5 x6 x10 x11) "Hentry".
  iExists x5, x6, x10, x11.
  iDestruct "Hentry" as "(Hsys&H1&H5&H6&H10&H11&Hmem&Hmmio&Hspec&HP&_)".
  iFrame.
  iSplit; last done.
  rewrite instr_pre'_eq /instr_pre'_def /=.
  iNext.
  iIntros "Hexit".
  iEval (rewrite /instr_pre'_def /=) in "Hreturn".
  iApply "Hreturn".
  iExists failureObservation.
  iFrame "Hexit".
  rewrite /writeFailureAllows. auto.
Qed.
Print Assumptions write_failure_tail_state_correct.
