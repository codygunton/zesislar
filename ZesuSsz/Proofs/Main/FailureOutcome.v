Require Import ZesuSsz.Automation.All.
Require Import ZesuMachineMap.Machine.
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Contracts.Endpoints.
Require Import ZesuSsz.Proofs.Main.Resources.
Require Import ZesuSsz.Proofs.Main.OutcomeCalls.
Require Import ZesuSsz.Proofs.Main.FailureFinish.
Require Import ZesuSsz.Proofs.WriteFailure.WriteFailure.
Require Import ZesuSsz.Proofs.WriteFailure.TraceContract.
Require Import ZesuSsz.Export.Snapshots.

Definition mainFailureWriterFrame `{!islaG Sigma} `{!threadG}
    (sp : bv 64) (P : iProp Sigma) : iProp Sigma :=
  ("x2" ↦ᵣ RVal_Bits sp ∗ mmio_range (machineExitAddress defaultMap) 8 ∗ P)%I.

Definition mainFailureOutcomeResources `{!islaG Sigma} `{!threadG}
    (tail : spec) (sp ra : bv 64) (P : iProp Sigma) :
    IslarisContractResources unit unit := {|
  islarisCode :=
    (([∗ list] i ∈ main_write_failure_instrs, instr i.1 (Some i.2)) ∗
     islarisCode _ _ (writeFailureTailResources
       (scons (SWriteMem (BV 64 (machineExitAddress defaultMap)) (BV 64 0)) tail)
       (mainFailureWriterFrame sp P)) ∗
     islarisCode _ _ (mainFailureFinishResources tail sp P))%I;
  islarisEntry := fun _ =>
    (∃ (x5 x6 a0 a1 : bv 64),
     mainCallRegisters sp ra a0 a1 ∗
     "x5" ↦ᵣ RVal_Bits x5 ∗ "x6" ↦ᵣ RVal_Bits x6 ∗
     0x177c8 ↦ₘ∗ failureMemory ∗ mmio_range (machineOutputAddress defaultMap) 16 ∗
     mmio_range (machineExitAddress defaultMap) 8 ∗
     spec_trace (writeOutputEvents (BV 64 0x177c8) (BV 64 6) failureMemory
       (scons (SWriteMem (BV 64 (machineExitAddress defaultMap)) (BV 64 0)) tail)) ∗ P ∗ True)%I;
  islarisExit := fun _ _ =>
    islarisExit _ _ (mainFailureFinishResources tail sp P) tt tt
|}.

Theorem main_failure_outcome_state_correct `{!islaG Sigma} `{!threadG}
    (tail : spec) (sp ra : bv 64) (P : iProp Sigma) :
  ⊢ IslarisContractSpec 0x14d1c 0x101d0 (fun _ _ => True%type)
    (mainFailureOutcomeResources tail sp ra P).
Proof.
  rewrite /IslarisContractSpec /mainFailureOutcomeResources /=.
  iIntros "(Hcall&Hwriter&Hfinish)" (args).
  iPoseProof (write_failure_tail_state_correct
    (scons (SWriteMem (BV 64 (machineExitAddress defaultMap)) (BV 64 0)) tail)
    (mainFailureWriterFrame sp P) with "Hwriter") as "Hwriter".
  iPoseProof (main_failure_finish_state_correct tail sp P with "Hfinish") as "Hfinish".
  rewrite instr_pre'_eq /instr_pre'_def /=.
  iIntros "[Hentry Hreturn]".
  iDestruct "Hentry" as (x5 x6 a0 a1)
    "(Hregs&H5&H6&Hmem&Houtput&Hexit&Hspec&HP&_)".
  let F := constr:(("x5" ↦ᵣ RVal_Bits x5 ∗ "x6" ↦ᵣ RVal_Bits x6 ∗
    0x177c8 ↦ₘ∗ failureMemory ∗ mmio_range (machineOutputAddress defaultMap) 16 ∗
    mmio_range (machineExitAddress defaultMap) 8 ∗
    spec_trace (writeOutputEvents (BV 64 0x177c8) (BV 64 6) failureMemory
      (scons (SWriteMem (BV 64 (machineExitAddress defaultMap)) (BV 64 0)) tail)) ∗ P ∗
    instr_pre 0x101d0 (∃ outcome : unit, ⌜True⌝ ∗
      islarisExit _ _ (mainFailureFinishResources tail sp P) tt tt))%I) in
  iPoseProof (main_write_failure_call_correct_with_frame sp ra a0 a1 F
    with "Hcall [Hwriter Hfinish]") as "Hbody".
  { rewrite instr_pre'_eq /instr_pre'_def /= /mainCallRegisters.
    iIntros "((Hsys&H1&H2&H10&H11&_)&(H5&H6&Hmem&Houtput&Hexit&Hspec&HP&Hreturn)&_)".
    iApply ("Hwriter" $! {| failureReturnAddress := 0x14d24 |}).
    rewrite /writeFailureTailResources /mainFailureWriterFrame /=.
    iSplitL "Hsys H1 H2 H5 H6 H10 H11 Hmem Houtput Hexit Hspec HP".
    { iSplit; first done. iExists x5, x6, a0, a1. iFrame. }
    rewrite /instr_pre'_def /=.
    iNext. iIntros "Hexit".
    iDestruct "Hexit" as (bytes) "[_ [_ Hexit]]".
    iDestruct "Hexit" as
      "(Hsys&H1&H5&H10&H11&Hmem&Houtput&Hspec&(H6&(H2&Hexit&HP)&_)&_)".
    iApply ("Hfinish" $! tt).
    rewrite /mainFailureFinishResources /mainCallRegisters /=.
    iFrame. }
  iEval (rewrite instr_pre'_eq /instr_pre'_def /=) in "Hbody".
  iApply "Hbody". iFrame.
Qed.
Print Assumptions main_failure_outcome_state_correct.
