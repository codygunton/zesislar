Require Import ZesuSsz.Automation.All.
Require Import ZesuMachineMap.Machine.
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Contracts.Endpoints.
Require Import ZesuSsz.Proofs.Main.Resources.
Require Import ZesuSsz.Proofs.Main.OutcomeCalls.
Require Import ZesuSsz.Proofs.ZkvmExit.ZkvmExit.
Require Import ZesuSsz.Proofs.ZkvmExit.TraceContract.
Require Import ZesuSsz.Export.Snapshots.

Definition mainSuccessTerminalFrame `{!islaG Sigma} `{!threadG}
    (sp a1 x6 : bv 64) (P : iProp Sigma) : iProp Sigma :=
  ("x1" ↦ᵣ RVal_Bits (BV 64 0x14d1c) ∗ "x2" ↦ᵣ RVal_Bits sp ∗
   "x6" ↦ᵣ RVal_Bits x6 ∗ "x11" ↦ᵣ RVal_Bits a1 ∗
   P)%I.

Definition mainSuccessFinishResources `{!islaG Sigma} `{!threadG}
    (tail : spec) (sp a0 a1 x5 x6 : bv 64) (P : iProp Sigma) :
    IslarisContractResources unit unit := {|
  islarisCode :=
    (([∗ list] i ∈ main_success_exit_instrs, instr i.1 (Some i.2)) ∗
     islarisCode _ _ (zkvmExitTailResources tail (mainSuccessTerminalFrame sp a1 x6 P)))%I;
  islarisEntry := fun _ =>
    (mainCallRegisters sp (BV 64 0x14d10) a0 a1 ∗
     "x5" ↦ᵣ RVal_Bits x5 ∗
     "x6" ↦ᵣ RVal_Bits x6 ∗
     mmio_range (machineExitAddress defaultMap) 8 ∗
     spec_trace (scons (SWriteMem (BV 64 (machineExitAddress defaultMap)) (BV 64 0)) tail) ∗ P ∗ True)%I;
  islarisExit := fun _ _ =>
    islarisExit _ _ (zkvmExitTailResources tail (mainSuccessTerminalFrame sp a1 x6 P))
      {| zkvmExitCode := 0 |} tt
|}.

Theorem main_success_finish_state_correct `{!islaG Sigma} `{!threadG}
    (tail : spec) (sp a0 a1 x5 x6 : bv 64) (P : iProp Sigma) :
  ⊢ IslarisContractSpec 0x14d10 0x101d0 (fun _ _ => True%type)
    (mainSuccessFinishResources tail sp a0 a1 x5 x6 P).
Proof.
  rewrite /IslarisContractSpec /mainSuccessFinishResources /=.
  iIntros "[Hglue HexitCode]" (args).
  iPoseProof (zkvm_exit_tail_state_correct tail (mainSuccessTerminalFrame sp a1 x6 P)) as "HnativeSpec".
  iPoseProof ("HnativeSpec" with "HexitCode") as "Hnative".
  rewrite instr_pre'_eq /instr_pre'_def /=.
  iIntros "[(Hregisters&H5&H6&Hexit&Hspec&HP&_) Hreturn]".
  let F := constr:(("x5" ↦ᵣ RVal_Bits x5 ∗
    "x6" ↦ᵣ RVal_Bits x6 ∗ mmio_range (machineExitAddress defaultMap) 8 ∗
    spec_trace (scons (SWriteMem (BV 64 (machineExitAddress defaultMap)) (BV 64 0)) tail) ∗ P ∗
    instr_pre 0x101d0 (∃ outcome : unit,
      ⌜True⌝ ∗ islarisExit _ _ (zkvmExitTailResources tail (mainSuccessTerminalFrame sp a1 x6 P))
        {| zkvmExitCode := 0 |} tt))%I) in
  iPoseProof (main_success_exit_call_correct_with_frame sp (BV 64 0x14d10)
    a0 a1 F with "Hglue [Hnative]") as "Hbody".
  { rewrite instr_pre'_eq /instr_pre'_def /= /mainCallRegisters.
    iIntros "((Hsys&H1&H2&H10&H11&_)&(H5&H6&Hexit&Hspec&HP&Hreturn)&_)".
    iApply ("Hnative" $! {| zkvmExitCode := 0 |}).
    rewrite /zkvmExitTailResources /mainSuccessTerminalFrame /=.
    iSplitR "Hreturn"; last iExact "Hreturn".
    iExists (BV 64 0), x5, (BV 64 0).
    iFrame. iPureIntro. vm_compute. reflexivity. }
  iEval (rewrite instr_pre'_eq /instr_pre'_def /=) in "Hbody".
  iApply "Hbody". iFrame.
Qed.
Print Assumptions main_success_finish_state_correct.
