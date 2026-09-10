Require Import isla.riscv64.riscv64.
From IslaTraces.write_failure Require Import instrs.
Require Import ZesuSsz.Contracts.IslarisMachine.
Require Import ZesuSsz.Generated.Level1.
Require Import ZesuSsz.Contracts.Endpoints.

Definition failureObservation : ByteString :=
  [0x5a; 0x53; 0x53; 0x5a; 0x01; 0x00].

Definition failureMemory : list (bv 8) :=
  [BV 8 0x5a; BV 8 0x53; BV 8 0x53; BV 8 0x5a; BV 8 0x01; BV 8 0x00].

Definition write_failure_resources `{!islaG Sigma} `{!threadG} :
    IslarisContractResources WriteFailureArgs ByteString := {|
  islarisCode :=
    (instr 0x161c0 (Some a161c0) ∗ instr 0x161c4 (Some a161c4) ∗
     instr 0x161c8 (Some a161c8) ∗ instr 0x161cc (Some a161cc) ∗
     instr 0x161d0 (Some a161d0) ∗ instr 0x10190 (Some a10190) ∗
     instr 0x10194 (Some a10194) ∗ instr 0x10198 (Some a10198) ∗
     instr 0x1019c (Some a1019c) ∗ instr 0x101a0 (Some a101a0))%I;
  islarisEntry := fun args =>
    (∃ (old_x5 old_x6 old_x10 old_x11 old_pointer old_length : bv 64),
      ⌜failureReturnAddress args = 0x14d24⌝ ∗
      reg_col zesu_zero_based_sys_regs ∗
      "x1" ↦ᵣ RVal_Bits (BV 64 0x14d24) ∗
      "x5" ↦ᵣ RVal_Bits old_x5 ∗ "x6" ↦ᵣ RVal_Bits old_x6 ∗
      "x10" ↦ᵣ RVal_Bits old_x10 ∗ "x11" ↦ᵣ RVal_Bits old_x11 ∗
      0x177c8 ↦ₘ∗ failureMemory ∗
      0x2401a0c0 ↦ₘ old_pointer ∗ 0x2401a0c8 ↦ₘ old_length)%I;
  islarisExit := fun args bytes =>
    (⌜failureReturnAddress args = 0x14d24⌝ ∗
     ⌜bytes = failureObservation⌝ ∗
     reg_col zesu_zero_based_sys_regs ∗
     "x1" ↦ᵣ RVal_Bits (BV 64 0x14d24) ∗
     "x5" ↦ᵣ RVal_Bits (BV 64 0x2401a0b8) ∗
     "x6" ↦ᵣ RVal_Bits (BV 64 0x101cc) ∗
     "x10" ↦ᵣ RVal_Bits (BV 64 0x177c8) ∗
     "x11" ↦ᵣ RVal_Bits (BV 64 6) ∗
     0x177c8 ↦ₘ∗ failureMemory ∗
     0x2401a0c0 ↦ₘ (BV 64 0x177c8) ∗
     0x2401a0c8 ↦ₘ (BV 64 6))%I
|}.

Definition writeFailureAllows
    (_ : WriteFailureArgs) (bytes : ByteString) : Prop :=
  bytes = failureObservation.

Theorem write_failure_state_correct `{!islaG Sigma} `{!threadG} :
  ⊢ IslarisContractSpec 0x161c0 0x14d24
    writeFailureAllows write_failure_resources.
Proof.
  rewrite /IslarisContractSpec /write_failure_resources /=.
  iStartProof.
  iIntros "(Hi1&Hi2&Hi3&Hi4&Hi5&Hi6&Hi7&Hi8&Hi9&Hi10)" (args).
  repeat liAStep; liShow.
  Unshelve. all: prepare_sidecond.
  all: try bv_solve.
  Unshelve.
  iExists (failureObservation, tt)ₗ.
  red_li_prod.
  iSplit; first done.
  iSplit; first done.
  iSplit; first done.
  replace LET5 with (BV 64 0x101cc) by bv_solve.
  replace LET2 with (BV 64 0x177c8) by bv_solve.
  replace (bv_unsigned LET14) with 0x2401a0c0 by bv_solve.
  replace LET12 with (BV 64 0x2401a0b8) by bv_solve.
  replace (bv_unsigned LET18) with 0x2401a0c8 by bv_solve.
  iFrame.
Qed.

Definition writeFailureControlFlow : list (Z * Z) := [
  (0x161c0, 0x161c4); (0x161c4, 0x161c8);
  (0x161c8, 0x161cc); (0x161cc, 0x161d0);
  (0x161d0, 0x10190); (0x10190, 0x10194);
  (0x10194, 0x10198); (0x10198, 0x1019c);
  (0x1019c, 0x101a0); (0x101a0, 0x14d24)
].

Definition writeFailureInstructionStep (fromPc toPc : Z) : Prop :=
  List.In (fromPc, toPc) writeFailureControlFlow.

Definition writeFailureModel :
    IslarisContractModel WriteFailureArgs ByteString := {|
  islarisContractAllows := writeFailureAllows;
  islarisContractStep := writeFailureInstructionStep;
  islarisContractResources := fun Sigma HG HT =>
    @write_failure_resources Sigma HG HT
|}.

Definition writeFailureCorrectness : Prop :=
  IslarisContractCorrect 0x161c0 0x14d24 writeFailureModel.

Definition writeFailurePath : list Z := [
  0x161c0; 0x161c4; 0x161c8; 0x161cc; 0x161d0;
  0x10190; 0x10194; 0x10198; 0x1019c; 0x101a0; 0x14d24
].

Lemma writeFailureTermination :
  InstructionPathCertificate writeFailureInstructionStep
    (PcInRanges writeFailureExecutionPcRanges)
    (PcInList writeFailureExitPcs) 0x161c0 10.
Proof.
  exists writeFailurePath. split; first reflexivity. split.
  - unfold writeFailurePath.
    solve_instruction_path ltac:(
      cbn [writeFailureInstructionStep writeFailureControlFlow];
      repeat first [left; reflexivity | right]).
  - split.
    + apply Forall_forall. intros pc Hpc.
      unfold writeFailurePath in Hpc.
      apply elem_of_list_In in Hpc. cbn in Hpc.
      intuition subst pc.
      all: unfold PcInRanges.
      all: first
        [ solve [eexists 0x161c0, 0x161d4; split; [cbn; auto | lia]]
        | solve [eexists 0x10190, 0x101c4; split; [cbn; auto | lia]] ].
    + split.
      * eexists 0x14d24. split; [reflexivity | cbn; auto].
      * split; [reflexivity | lia].
Qed.

Theorem level1WriteFailure :
  exists bound : nat, Nat.lt bound level1ContractFuel /\
    NativeContractAssumption writeFailureCorrectness
      writeFailureInstructionStep
      (PcInRanges writeFailureExecutionPcRanges)
      (PcInList writeFailureExitPcs)
      ZesuSsz.Generated.Level1.writeFailureEntry bound.
Proof.
  exists 10%nat. split.
  - unfold level1ContractFuel.
    pose proof (Nat.pow_gt_lin_r 2 160 ltac:(lia)) as Hbound. lia.
  - apply nativeContractBridge.
    + intros Sigma HG HT. apply write_failure_state_correct.
    + exact writeFailureTermination.
Qed.
