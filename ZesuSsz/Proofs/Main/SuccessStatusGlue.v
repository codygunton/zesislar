Require Import ZesuSsz.Automation.All.
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Contracts.Endpoints.
Require Import ZesuSsz.Proofs.Main.Resources.
Require Import ZesuSsz.Proofs.Main.Dispatch.
Require Import ZesuSsz.Proofs.Main.OutcomeCalls.
Definition mainSuccessStatusGlueResources `{!islaG Sigma} `{!threadG}
    (sp ra a0 a1 : bv 64) (P : iProp Sigma) :
    IslarisContractResources unit unit := {|
  islarisCode := (([∗ list] i ∈ mainDispatchInstrs, instr i.1 (Some i.2)) ∗
    ([∗ list] i ∈ main_write_success_instrs, instr i.1 (Some i.2)))%I;
  islarisEntry := fun _ => (mainCallRegisters sp ra a0 a1 ∗
    mainDispatchMemory sp (BV 16 0) ∗ P ∗ True)%I;
  islarisExit := fun _ _ => (mainCallRegisters sp (BV 64 0x14d10)
    (sp + BV 64 32)%bv a1 ∗ mainDispatchMemory sp (BV 16 0) ∗ P ∗ True)%I
|}.
Lemma main_success_status_glue_state_correct `{!islaG Sigma} `{!threadG}
    (sp ra a0 a1 : bv 64) (P : iProp Sigma) :
  ⊢ IslarisContractSpec 0x14cfc 0x14d30 (fun _ _ => True%type)
    (mainSuccessStatusGlueResources sp ra a0 a1 P).
Proof.
  rewrite /IslarisContractSpec /mainSuccessStatusGlueResources
    /mainCallRegisters /mainDispatchMemory /mainDispatchInstrs
    /main_write_success_instrs /=.
  zesu_block. all: exfalso; apply H6; apply bv_eq; vm_compute; reflexivity.
Qed.
Print Assumptions main_success_status_glue_state_correct.
