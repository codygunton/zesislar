Require Import ZesuSsz.Automation.All.
Require Import isla.riscv64.riscv64.
From IslaTraces.startup Require Import instrs.
Require Import ZesuSsz.Contracts.Endpoints.
Require Import ZesuSsz.Contracts.IslarisMachine.

Definition startupInstrs : list (Z * isla_trace) :=
  [(0x10120, a10120); (0x10124, a10124); (0x10128, a10128)].

Definition startupResources `{!islaG Sigma} `{!threadG} :
    IslarisContractResources (bv 64 * bv 64) unit := {|
  islarisCode := ([∗ list] i ∈ startupInstrs, instr i.1 (Some i.2))%I;
  islarisEntry := fun (old : bv 64 * bv 64) =>
    (reg_col zesu_sys_regs ∗
     "x1" ↦ᵣ RVal_Bits old.1 ∗ "x3" ↦ᵣ RVal_Bits old.2 ∗ True)%I;
  islarisExit := fun (_ : bv 64 * bv 64) (_ : unit) =>
    (reg_col zesu_sys_regs ∗
     "x1" ↦ᵣ RVal_Bits (BV 64 0x1012c) ∗
     "x3" ↦ᵣ RVal_Bits (BV 64 0x19800) ∗ True)%I
|}.

Definition startupModel : IslarisContractModel (bv 64 * bv 64) unit := {|
  islarisContractAllows := fun _ _ => True;
  islarisContractStep := fun _ nextPc => nextPc = 0x14cb0;
  islarisContractResources := fun Sigma HG HT => @startupResources Sigma HG HT
|}.

Theorem startup_state_correct `{!islaG Sigma} `{!threadG} :
  ⊢ IslarisContractSpec 0x10120 0x14cb0
      (fun _ _ => True%type) startupResources.
Proof.
  rewrite /IslarisContractSpec /startupResources /startupInstrs /=.
  zesu_block.
Qed.

Theorem startup_correct : IslarisContractCorrect 0x10120 0x14cb0 startupModel.
Proof.
  intros Sigma HG HT. exact (@startup_state_correct Sigma HG HT).
Qed.

Print Assumptions startup_correct.

Definition startupFrameResources `{!islaG Sigma} `{!threadG}
    (P : iProp Sigma) : IslarisContractResources (bv 64 * bv 64) unit := {|
  islarisCode := ([∗ list] i ∈ startupInstrs, instr i.1 (Some i.2))%I;
  islarisEntry := fun (old : bv 64 * bv 64) =>
    (reg_col zesu_sys_regs ∗
     "x1" ↦ᵣ RVal_Bits old.1 ∗ "x3" ↦ᵣ RVal_Bits old.2 ∗ P ∗ True)%I;
  islarisExit := fun (_ : bv 64 * bv 64) (_ : unit) =>
    (reg_col zesu_sys_regs ∗
     "x1" ↦ᵣ RVal_Bits (BV 64 0x1012c) ∗
     "x3" ↦ᵣ RVal_Bits (BV 64 0x19800) ∗ P ∗ True)%I
|}.

Theorem startup_frame_state_correct `{!islaG Sigma} `{!threadG}
    (P : iProp Sigma) :
  ⊢ IslarisContractSpec 0x10120 0x14cb0
      (fun _ _ => True%type) (startupFrameResources P).
Proof.
  rewrite /IslarisContractSpec /startupFrameResources /startupInstrs /=.
  zesu_block.
Qed.

Print Assumptions startup_frame_state_correct.
