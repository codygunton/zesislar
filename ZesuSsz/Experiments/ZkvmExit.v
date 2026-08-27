From iris.program_logic Require Import language.
Require Import isla.riscv64.riscv64.
From IslaTraces.zkvm_exit Require Import instrs.
Require Import ZesuSsz.Contracts.Machine.
Require Import ZesuSsz.Generated.Level1.
Require Import ZesuSsz.Contracts.Level1.

Definition zkvm_exit_resources `{!islaG Sigma} `{!threadG} :
    IslarisContractResources ZkvmExitArgs unit := {|
  islarisCode :=
    (instr 0x101c4 (Some a101c4) ∗
     instr 0x101c8 (Some a101c8) ∗
     instr 0x101cc (Some a101cc))%I;
  islarisEntry := fun args =>
    (∃ (code old_x5 old_exit_code : bv 64),
      ⌜bv_unsigned code = zkvmExitCode args⌝ ∗
      reg_col zesu_zero_based_sys_regs ∗
      "x5" ↦ᵣ RVal_Bits old_x5 ∗
      "x10" ↦ᵣ RVal_Bits code ∗
      0x2401a0d0 ↦ₘ old_exit_code)%I;
  islarisExit := fun args _ =>
    (∃ (code : bv 64),
      ⌜bv_unsigned code = zkvmExitCode args⌝ ∗
      reg_col zesu_zero_based_sys_regs ∗
      "x5" ↦ᵣ RVal_Bits (BV 64 0x2401a0b8) ∗
      "x10" ↦ᵣ RVal_Bits code ∗
      0x2401a0d0 ↦ₘ code)%I
|}.

Definition zkvmExitAllows (_ : ZkvmExitArgs) (_ : unit) : Prop := True.

Theorem zkvm_exit_state_correct `{!islaG Sigma} `{!threadG} :
  ⊢ IslarisContractSpec 0x101c4 0x101d0
    zkvmExitAllows zkvm_exit_resources.
Proof.
  rewrite /IslarisContractSpec /zkvm_exit_resources /=.
  iStartProof.
  iIntros "(Hi1&Hi2&Hi3)" (args).
  repeat liAStep; liShow.
  Unshelve. all: prepare_sidecond.
  all: try bv_solve.
  Unshelve.
  iExists (code, tt)ₗ.
  red_li_prod.
  replace LET2 with (BV 64 0x2401a0b8) by bv_solve.
  replace (bv_unsigned LET4) with 0x2401a0d0 by bv_solve.
  iFrame. done.
Qed.

Definition zkvmExitModel : IslarisContractModel ZkvmExitArgs unit := {|
  islarisContractAllows := zkvmExitAllows;
  islarisContractStep := StraightLineInstructionStep;
  islarisContractResources := fun Sigma HG HT =>
    @zkvm_exit_resources Sigma HG HT
|}.

Definition zkvmExitCorrectness : Prop :=
  IslarisContractCorrect 0x101c4 0x101d0 zkvmExitModel.

Definition zkvmExitPath : list Z :=
  [0x101c4; 0x101c8; 0x101cc; 0x101d0].

Lemma zkvmExitTermination :
  InstructionPathCertificate StraightLineInstructionStep ZkvmExitExecutionPc
    (PcInList zkvmExitExitPcs) 0x101c4 3.
Proof.
  exists zkvmExitPath. split; first reflexivity. split.
  - unfold zkvmExitPath.
    solve_instruction_path ltac:(unfold StraightLineInstructionStep; lia).
  - split.
    + apply Forall_forall. intros pc Hpc.
      unfold zkvmExitPath in Hpc.
      apply elem_of_list_In in Hpc. cbn in Hpc.
      unfold ZkvmExitExecutionPc, PcInRanges. split.
      * eexists 0x101c4, 0x101d4. split; [cbn; auto | lia].
      * unfold zkvmExitTerminalPc. lia.
    + split.
      * eexists 0x101d0. split; [reflexivity | cbn; auto].
      * split; [reflexivity | lia].
Qed.

Theorem level1ZkvmExit :
  exists bound : nat, Nat.lt bound level1ContractFuel /\
    NativeContractAssumption zkvmExitCorrectness
      StraightLineInstructionStep ZkvmExitExecutionPc
      (PcInList zkvmExitExitPcs)
      ZesuSsz.Generated.Level1.zkvmExitEntry bound.
Proof.
  exists 3%nat. split.
  - unfold level1ContractFuel.
    pose proof (Nat.pow_gt_lin_r 2 160 ltac:(lia)) as Hbound. lia.
  - apply nativeContractBridge.
    + intros Sigma HG HT. apply zkvm_exit_state_correct.
    + exact zkvmExitTermination.
Qed.
