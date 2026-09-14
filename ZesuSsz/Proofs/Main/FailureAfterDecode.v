Require Import ZesuSsz.Automation.All.
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Contracts.Endpoints.
Require Import ZesuSsz.Proofs.Main.Resources.
Require Import ZesuSsz.Proofs.Main.Dispatch.
Require Import ZesuSsz.Proofs.Main.FailureOutcome.
Require Import ZesuSsz.Proofs.WriteFailure.WriteFailure.
Require Import ZesuSsz.Export.Snapshots.

Definition mainFailureAfterDecodeResources `{!islaG Sigma} `{!threadG}
    (tail : spec) (sp ra : bv 64) (status : bv 16) (P : iProp Sigma) :
    IslarisContractResources unit unit := {|
  islarisCode :=
    (([∗ list] i ∈ mainDispatchInstrs, instr i.1 (Some i.2)) ∗
     islarisCode _ _ (mainFailureOutcomeResources tail sp ra
       (mainDispatchMemory sp status ∗ P)))%I;
  islarisEntry := fun _ =>
    (⌜bv_unsigned status <> 0⌝ ∗ mainDispatchMemory sp status ∗
     islarisEntry _ _ (mainFailureOutcomeResources tail sp ra P) tt)%I;
  islarisExit := fun _ _ =>
    islarisExit _ _ (mainFailureOutcomeResources tail sp ra
      (mainDispatchMemory sp status ∗ P)) tt tt
|}.

Theorem main_failure_after_decode_state_correct `{!islaG Sigma} `{!threadG}
    (tail : spec) (sp ra : bv 64) (status : bv 16) (P : iProp Sigma) :
  ⊢ IslarisContractSpec 0x14cfc 0x101d0 (fun _ _ => True%type)
    (mainFailureAfterDecodeResources tail sp ra status P).
Proof.
  rewrite /IslarisContractSpec /mainFailureAfterDecodeResources /=.
  iIntros "[Hdispatch HoutcomeCode]" (args).
  iPoseProof (main_failure_outcome_state_correct tail sp ra
    (mainDispatchMemory sp status ∗ P) with "HoutcomeCode") as "Houtcome".
  rewrite instr_pre'_eq /instr_pre'_def /=.
  iIntros "[[%Hnonzero [Hstatus Hentry]] Hreturn]".
  iDestruct "Hentry" as (x5 x6 a0 a1)
    "(Hregs&H5&H6&Hmem&Houtput&Hexit&Hspec&HP&_)".
  let F := constr:(("x5" ↦ᵣ RVal_Bits x5 ∗ "x6" ↦ᵣ RVal_Bits x6 ∗
    0x177c8 ↦ₘ∗ failureMemory ∗ mmio_range 0x2401a0c0 16 ∗
    mmio_range 0x2401a0d0 8 ∗
    spec_trace (writeOutputEvents (BV 64 0x177c8) (BV 64 6) failureMemory
      (scons (SWriteMem (BV 64 0x2401a0d0) (BV 64 0)) tail)) ∗ P ∗
    instr_pre 0x101d0 (∃ outcome : unit, ⌜True⌝ ∗
      islarisExit _ _ (mainFailureOutcomeResources tail sp ra
        (mainDispatchMemory sp status ∗ P)) tt tt))%I) in
  iPoseProof (main_dispatch_failure_correct_with_frame sp ra a0 a1 status F
    with "Hdispatch [Houtcome]") as "Hbody".
  { rewrite instr_pre'_eq /instr_pre'_def /=.
    iIntros "(Hregs&Hstatus&_&(H5&H6&Hmem&Houtput&Hexit&Hspec&HP&Hreturn)&_)".
    iApply ("Houtcome" $! tt).
    rewrite /mainFailureOutcomeResources /=.
    iSplitL "Hregs Hstatus H5 H6 Hmem Houtput Hexit Hspec HP".
    { iExists x5, x6, (bv_zero_extend 64 status), a1. iFrame. }
    iExact "Hreturn". }
  iEval (rewrite instr_pre'_eq /instr_pre'_def /=) in "Hbody".
  iApply "Hbody". iFrame. done.
Qed.
Print Assumptions main_failure_after_decode_state_correct.
