Require Import ZesuSsz.Automation.All.
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Contracts.Endpoints.
Require Import ZesuSsz.Proofs.Main.Resources.
Require Import ZesuSsz.Proofs.Main.OutcomeCalls.
Require Import ZesuSsz.Proofs.WriteFailure.WriteFailure.
Require Import ZesuSsz.Proofs.ZkvmExit.ZkvmExit.
Require Import ZesuSsz.Proofs.ZkvmExit.TraceContract.
Require Import ZesuSsz.Export.Snapshots.

Definition mainFailureTerminalFrame `{!islaG Sigma} `{!threadG}
    (sp : bv 64) (P : iProp Sigma) : iProp Sigma :=
  ("x1" ↦ᵣ RVal_Bits (BV 64 0x14d30) ∗ "x2" ↦ᵣ RVal_Bits sp ∗
   "x6" ↦ᵣ RVal_Bits (BV 64 0x101cc) ∗ "x11" ↦ᵣ RVal_Bits (BV 64 6) ∗
   0x177c8 ↦ₘ∗ failureMemory ∗ mmio_range 0x2401a0c0 16 ∗ P)%I.

Definition mainFailureFinishResources `{!islaG Sigma} `{!threadG}
    (tail : spec) (sp : bv 64) (P : iProp Sigma) :
    IslarisContractResources unit unit := {|
  islarisCode :=
    (([∗ list] i ∈ main_failure_exit_instrs, instr i.1 (Some i.2)) ∗
     islarisCode _ _ (zkvmExitTailResources tail (mainFailureTerminalFrame sp P)))%I;
  islarisEntry := fun _ =>
    (mainCallRegisters sp (BV 64 0x14d24) (BV 64 0x177c8) (BV 64 6) ∗
     "x5" ↦ᵣ RVal_Bits (BV 64 0x2401a0b8) ∗
     "x6" ↦ᵣ RVal_Bits (BV 64 0x101cc) ∗
     0x177c8 ↦ₘ∗ failureMemory ∗ mmio_range 0x2401a0c0 16 ∗
     mmio_range 0x2401a0d0 8 ∗
     spec_trace (scons (SWriteMem (BV 64 0x2401a0d0) (BV 64 0)) tail) ∗ P ∗ True)%I;
  islarisExit := fun _ _ =>
    islarisExit _ _ (zkvmExitTailResources tail (mainFailureTerminalFrame sp P))
      {| zkvmExitCode := 0 |} tt
|}.

Theorem main_failure_finish_state_correct `{!islaG Sigma} `{!threadG}
    (tail : spec) (sp : bv 64) (P : iProp Sigma) :
  ⊢ IslarisContractSpec 0x14d24 0x101d0 (fun _ _ => True%type)
    (mainFailureFinishResources tail sp P).
Proof.
  rewrite /IslarisContractSpec /mainFailureFinishResources /=.
  iIntros "[Hglue HexitCode]" (args).
  iPoseProof (zkvm_exit_tail_state_correct tail (mainFailureTerminalFrame sp P)) as "HnativeSpec".
  iPoseProof ("HnativeSpec" with "HexitCode") as "Hnative".
  rewrite instr_pre'_eq /instr_pre'_def /=.
  iIntros "[(Hregisters&H5&H6&Hmemory&Houtput&Hexit&Hspec&HP&_) Hreturn]".
  let F := constr:(("x5" ↦ᵣ RVal_Bits (BV 64 0x2401a0b8) ∗
    "x6" ↦ᵣ RVal_Bits (BV 64 0x101cc) ∗ 0x177c8 ↦ₘ∗ failureMemory ∗
    mmio_range 0x2401a0c0 16 ∗ mmio_range 0x2401a0d0 8 ∗
    spec_trace (scons (SWriteMem (BV 64 0x2401a0d0) (BV 64 0)) tail) ∗ P ∗
    instr_pre 0x101d0 (∃ outcome : unit,
      ⌜True⌝ ∗ islarisExit _ _ (zkvmExitTailResources tail (mainFailureTerminalFrame sp P))
        {| zkvmExitCode := 0 |} tt))%I) in
  iPoseProof (main_failure_exit_call_correct_with_frame sp (BV 64 0x14d24)
    (BV 64 0x177c8) (BV 64 6) F with "Hglue [Hnative]") as "Hbody".
  { rewrite instr_pre'_eq /instr_pre'_def /= /mainCallRegisters.
    iIntros "((Hsys&H1&H2&H10&H11&_)&(H5&H6&Hmemory&Houtput&Hexit&Hspec&HP&Hreturn)&_)".
    iApply ("Hnative" $! {| zkvmExitCode := 0 |}).
    rewrite /zkvmExitTailResources /mainFailureTerminalFrame /=.
    iSplitR "Hreturn"; last iExact "Hreturn".
    iExists (BV 64 0), (BV 64 0x2401a0b8), (BV 64 0).
    iFrame. iPureIntro. vm_compute. reflexivity. }
  iEval (rewrite instr_pre'_eq /instr_pre'_def /=) in "Hbody".
  iApply "Hbody". iFrame.
Qed.
Print Assumptions main_failure_finish_state_correct.
