Require Import ZesuSsz.Automation.All.
From iris.program_logic Require Import language.
Require Import isla.riscv64.riscv64.
From IslaTraces.zkvm_exit Require Import instrs.
Require Import ZesuSsz.Contracts.Machine.
Require Import ZesuSsz.Generated.Level1.
Require Import ZesuSsz.Contracts.Endpoints.

Definition zesu_sys_regs : list (reg_kind * valu_shape) := [
  (KindReg "rv_enable_pmp", ExactShape (RVal_Bool false));
  (KindReg "rv_enable_misaligned_access", ExactShape (RVal_Bool false));
  (KindReg "rv_ram_base", ExactShape (RVal_Bits (BV 64 0x0)));
  (KindReg "rv_ram_size", ExactShape (RVal_Bits (BV 64 0x40000000)));
  (KindReg "rv_rom_base", ExactShape (RVal_Bits (BV 64 0x1000)));
  (KindReg "rv_rom_size", ExactShape (RVal_Bits (BV 64 0x100)));
  (KindReg "rv_clint_base", ExactShape (RVal_Bits (BV 64 0x2000000)));
  (KindReg "rv_clint_size", ExactShape (RVal_Bits (BV 64 0xc0000)));
  (KindReg "rv_htif_tohost", ExactShape (RVal_Bits (BV 64 0x40001000)));
  (KindReg "cur_privilege", ExactShape (RVal_Enum "Machine"));
  (KindReg "misa", ExactShape (RegVal_Struct [
    ("bits", RVal_Bits (BV 64 0x8000000000001100))]));
  (KindReg "mstatus", StructShape [("bits", MaskShape 64 0x20000 0)]);
  (KindReg "satp", BitsShape 64)
].

Definition zkvm_exit_resources `{!islaG Sigma} `{!threadG} :
    IslarisContractResources ZkvmExitArgs unit := {|
  islarisCode :=
    (instr 0x101c4 (Some a101c4) ∗
     instr 0x101c8 (Some a101c8) ∗
     instr 0x101cc (Some a101cc))%I;
  islarisEntry := fun args =>
    (∃ (code old_x5 old_exit_code : bv 64),
      ⌜bv_unsigned code = zkvmExitCode args⌝ ∗
      reg_col zesu_sys_regs ∗
      "x5" ↦ᵣ RVal_Bits old_x5 ∗
      "x10" ↦ᵣ RVal_Bits code ∗
      0x2401a0d0 ↦ₘ old_exit_code)%I;
  islarisExit := fun args _ =>
    (∃ (code : bv 64),
      ⌜bv_unsigned code = zkvmExitCode args⌝ ∗
      reg_col zesu_sys_regs ∗
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
  exists zkvmExitPath. repeat split.
  - repeat constructor; unfold StraightLineInstructionStep; lia.
  - cbn [zkvmExitPath].
    constructor.
    + unfold ZkvmExitExecutionPc, PcInRanges. split.
      * eexists 0x101c4, 0x101d4. split; [cbn; auto | lia].
      * unfold zkvmExitTerminalPc. lia.
    + constructor.
      * unfold ZkvmExitExecutionPc, PcInRanges. split.
        -- eexists 0x101c4, 0x101d4. split; [cbn; auto | lia].
        -- unfold zkvmExitTerminalPc. lia.
      * constructor.
        -- unfold ZkvmExitExecutionPc, PcInRanges. split.
           ++ eexists 0x101c4, 0x101d4. split; [cbn; auto | lia].
           ++ unfold zkvmExitTerminalPc. lia.
        -- constructor.
  - eexists 0x101d0. split; [reflexivity | cbn; auto].
  - lia.
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
