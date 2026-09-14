Require Import ZesuSsz.Automation.All.
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Contracts.Endpoints.
Require Import ZesuSsz.Proofs.Main.AllocatorAdapter.
Definition mainAllocatorGuardedResources `{!islaG Sigma} `{!threadG}
    (sp inputPointer inputSize : bv 64) (P : iProp Sigma) :
    IslarisContractResources unit unit := {|
  islarisCode := ([∗ list] i ∈ IslaTraces.allocator_get.instrs.instr_map, instr i.1 (Some i.2))%I;
  islarisEntry := fun _ => (mainAllocatorEntry sp inputPointer inputSize ∗ P ∗ True)%I;
  islarisExit := fun _ _ => (mainAllocatorExit sp inputPointer inputSize ∗ P ∗ True)%I
|}.
Theorem main_allocator_guarded_state_correct `{!islaG Sigma} `{!threadG}
    (sp inputPointer inputSize : bv 64) (P : iProp Sigma) :
  ⊢ IslarisContractSpec 0x14ccc 0x14cec (fun _ _ => True%type)
    (mainAllocatorGuardedResources sp inputPointer inputSize P).
Proof.
  rewrite /IslarisContractSpec /mainAllocatorGuardedResources
    /mainAllocatorEntry /mainAllocatorExit /IslaTraces.allocator_get.instrs.instr_map /=.
  zesu_block.
Qed.
Print Assumptions main_allocator_guarded_state_correct.
