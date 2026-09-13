Require Import ZesuSsz.Automation.All.
Require Import isla.riscv64.riscv64.
From IslaTraces.allocator_get Require Import instrs.
Require Import ZesuSsz.Contracts.IslarisMachine.
Require Import ZesuSsz.Generated.Level1.
Require Import ZesuSsz.Contracts.Endpoints.

Definition allocator_get_resources `{!islaG Sigma} `{!threadG} :
    IslarisContractResources AllocatorGetArgs AllocatorGetOutcome := {|
  islarisCode :=
    (instr 0x14ccc (Some a14ccc) ∗
     instr 0x14cd0 (Some a14cd0) ∗
     instr 0x14cd4 (Some a14cd4) ∗
     instr 0x14cd8 (Some a14cd8) ∗
     instr 0x14cdc (Some a14cdc) ∗
     instr 0x14ce0 (Some a14ce0) ∗
     instr 0x14ce4 (Some a14ce4) ∗
     instr 0x14ce8 (Some a14ce8))%I;
  islarisEntry := fun args =>
    (∃ (sp old_x10 old_x11 old_x12 old_x13 stack0 stack8 : bv 64),
      ⌜bv_unsigned sp = allocatorStackPointer args⌝ ∗
      reg_col zesu_ram_sys_regs ∗
      "x2" ↦ᵣ RVal_Bits sp ∗
      "x10" ↦ᵣ RVal_Bits old_x10 ∗
      "x11" ↦ᵣ RVal_Bits old_x11 ∗
      "x12" ↦ᵣ RVal_Bits old_x12 ∗
      "x13" ↦ᵣ RVal_Bits old_x13 ∗
      bv_unsigned sp ↦ₘ stack0 ∗
      (bv_unsigned sp + 8) ↦ₘ stack8 ∗
      (bv_unsigned sp + 16) ↦ₘ? 8 ∗
      (bv_unsigned sp + 24) ↦ₘ? 8 ∗
      ⌜bv_unsigned sp `mod` 8 = 0⌝ ∗
      ⌜(0x20000000 ≤ bv_unsigned sp)%Z⌝ ∗
      ⌜(bv_unsigned sp + 24 < 0x40000000)%Z⌝)%I;
  islarisExit := fun args outcome =>
    (∃ (sp stack0 stack8 : bv 64),
      ⌜bv_unsigned sp = allocatorStackPointer args⌝ ∗
      ⌜outcome = Build_AllocatorGetOutcome 0x2401a0b0 0x177a8⌝ ∗
      reg_col zesu_ram_sys_regs ∗
      "x2" ↦ᵣ RVal_Bits sp ∗
      "x10" ↦ᵣ RVal_Bits (BV 64 0x2401a0b0) ∗
      "x11" ↦ᵣ RVal_Bits (BV 64 0x177a8) ∗
      "x12" ↦ᵣ RVal_Bits stack0 ∗
      "x13" ↦ᵣ RVal_Bits stack8 ∗
      bv_unsigned sp ↦ₘ stack0 ∗
      (bv_unsigned sp + 8) ↦ₘ stack8 ∗
      (bv_unsigned sp + 16) ↦ₘ (BV 64 0x2401a0b0) ∗
      (bv_unsigned sp + 24) ↦ₘ (BV 64 0x177a8))%I
|}.

Definition allocatorGetAllows
    (_ : AllocatorGetArgs) (_ : AllocatorGetOutcome) : Prop := True.

Theorem allocator_get_state_correct `{!islaG Sigma} `{!threadG} :
  ⊢ IslarisContractSpec 0x14ccc 0x14cec
    allocatorGetAllows allocator_get_resources.
Proof.
  rewrite /IslarisContractSpec /allocator_get_resources /=.
  iStartProof.
  iIntros "(Hi1&Hi2&Hi3&Hi4&Hi5&Hi6&Hi7&Hi8)" (args).
  repeat lazymatch goal with
  | |- _ ⊢ WPasm tnil => fail 1
  | _ => zesu_liAStep
  end.
  liShow.
  iExists (Build_AllocatorGetOutcome 0x2401a0b0 0x177a8, tt)ₗ.
  red_li_prod.
  iSplit; first done.
  iExists sp, stack0, stack8.
  zesu_run.
  Unshelve. all: zesu_run.
Qed.
Print Assumptions allocator_get_state_correct.

Definition allocatorGetModel :
    IslarisContractModel AllocatorGetArgs AllocatorGetOutcome := {|
  islarisContractAllows := allocatorGetAllows;
  islarisContractStep := StraightLineInstructionStep;
  islarisContractResources := fun Sigma HG HT =>
    @allocator_get_resources Sigma HG HT
|}.

Definition allocatorGetCorrectness : Prop :=
  IslarisContractCorrect 0x14ccc 0x14cec allocatorGetModel.

Definition allocatorGetPath : list Z :=
  [0x14ccc; 0x14cd0; 0x14cd4; 0x14cd8; 0x14cdc;
   0x14ce0; 0x14ce4; 0x14ce8; 0x14cec].

Lemma allocatorGetTermination :
  InstructionPathCertificate StraightLineInstructionStep
    (PcInRanges allocatorGetExecutionPcRanges)
    (PcInList allocatorGetExitPcs) 0x14ccc 8.
Proof.
  exists allocatorGetPath. repeat split.
  - repeat constructor; unfold StraightLineInstructionStep; lia.
  - apply Forall_forall. intros pc Hpc.
    unfold PcInRanges. eexists 0x14ccc, 0x14cec. split.
    + cbn. auto.
    + unfold allocatorGetPath in Hpc. cbn in Hpc.
      apply elem_of_list_In in Hpc. cbn in Hpc. lia.
  - eexists 0x14cec. split; [reflexivity | cbn; auto].
  - lia.
Qed.

Theorem level1AllocatorGet :
  exists bound : nat, Nat.lt bound level1ContractFuel /\
    NativeContractAssumption allocatorGetCorrectness
      StraightLineInstructionStep
      (PcInRanges allocatorGetExecutionPcRanges)
      (PcInList allocatorGetExitPcs)
      ZesuSsz.Generated.Level1.allocatorGetEntry bound.
Proof.
  exists 8%nat. split.
  - unfold level1ContractFuel.
    pose proof (Nat.pow_gt_lin_r 2 160 ltac:(lia)) as Hbound. lia.
  - apply nativeContractBridge.
    + intros Sigma HG HT. apply allocator_get_state_correct.
    + exact allocatorGetTermination.
Qed.
