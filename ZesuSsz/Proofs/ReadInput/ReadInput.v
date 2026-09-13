Require Import ZesuSsz.Automation.All.
From Coq Require Import Lists.List ZArith.ZArith.
Require Import isla.riscv64.riscv64.
From IslaTraces.read_input Require Import instrs.
Require Import ZesuSsz.Contracts.IslarisMachine.
Require Import ZesuSsz.Generated.Level1.
Require Import ZesuSsz.Contracts.Endpoints.

Import ListNotations.

Definition readInputMemory (bytes : ByteString) : list (bv 8) :=
  List.map (Z_to_bv 8) bytes.

Definition readInputIoPointer : bv 64 :=
  (Z_to_bv 64 65868 + (BV 64 604020736) +
   (BV 64 18446744073709551468))%bv.

Lemma read_input_buffer_pointer_eq :
  (Z_to_bv 64 65856 + (BV 64 536911872) +
   (BV 64 18446744073709551296))%bv = BV 64 0x2001a000.
Proof. apply bv_eq. vm_compute. reflexivity. Qed.

Lemma read_input_io_pointer_eq :
  readInputIoPointer = BV 64 0x2401a0b8.
Proof. apply bv_eq. vm_compute. reflexivity. Qed.

#[local] Hint Rewrite read_input_buffer_pointer_eq
  : isla_coq_rewrite.

Definition read_input_resources `{!islaG Sigma} `{!threadG} :
    IslarisContractResources ReadInputArgs ReadInputOutcome := {|
  islarisCode :=
    (instr 0x10140 (Some a10140) ∗ instr 0x10144 (Some a10144) ∗
     instr 0x10148 (Some a10148) ∗ instr 0x1014c (Some a1014c) ∗
     instr 0x10150 (Some a10150) ∗ instr 0x10154 (Some a10154) ∗
     instr 0x10158 (Some a10158) ∗ instr 0x1015c (Some a1015c))%I;
  islarisEntry := fun args =>
    (∃ (bufferSlot sizeSlot sizeWord old_x5 old_x6
         oldBufferSlot oldSizeSlot savedWord : bv 64),
      ⌜bv_unsigned bufferSlot = readBufferSlot args⌝ ∗
      ⌜bv_unsigned sizeSlot = readSizeSlot args⌝ ∗
      ⌜readReturnAddress args = 0x14ccc⌝ ∗
      ⌜readSizeSlot args = (readBufferSlot args + 8)%Z⌝ ∗
      ⌜Z.modulo (readBufferSlot args) 8 = 0⌝ ∗
      ⌜bv_extract 0 3 bufferSlot = BV 3 0⌝ ∗
      ⌜bv_extract 0 3 sizeSlot = BV 3 0⌝ ∗
      ⌜(0x20000000 <= readBufferSlot args)%Z⌝ ∗
      ⌜(readSizeSlot args < 0x40000000)%Z⌝ ∗
      ⌜(0x20000000 <= bv_unsigned bufferSlot)%Z⌝ ∗
      ⌜(bv_unsigned bufferSlot < 0x40000000)%Z⌝ ∗
      ⌜(bv_unsigned sizeSlot < 0x40000000)%Z⌝ ∗
      ⌜bv_unsigned sizeWord = Z.of_nat (length (readInputBytes args))⌝ ∗
      ⌜(length (readInputBytes args) <= maxSszInputSize)%nat⌝ ∗
      reg_col zesu_ram_sys_regs ∗
      "x1" ↦ᵣ RVal_Bits (BV 64 0x14ccc) ∗
      "x5" ↦ᵣ RVal_Bits old_x5 ∗
      "x6" ↦ᵣ RVal_Bits old_x6 ∗
      "x10" ↦ᵣ RVal_Bits bufferSlot ∗
      "x11" ↦ᵣ RVal_Bits sizeSlot ∗
      bv_unsigned (bufferSlot + (BV 64 0)) ↦ₘ oldBufferSlot ∗
      bv_unsigned (sizeSlot + (BV 64 0)) ↦ₘ oldSizeSlot ∗
      bv_unsigned (readInputIoPointer + (BV 64 0)) ↦ₘ sizeWord ∗
      0x2001a000 ↦ₘ∗ readInputMemory (readInputBytes args) ∗
      readSavedFrameAddress args ↦ₘ savedWord ∗
      ⌜bv_unsigned savedWord = readSavedReturnAddress args⌝ ∗ True)%I;
  islarisExit := fun args outcome =>
    (∃ (bufferSlot sizeSlot sizeWord savedWord : bv 64),
      ⌜bv_unsigned bufferSlot = readBufferSlot args⌝ ∗
      ⌜bv_unsigned sizeSlot = readSizeSlot args⌝ ∗
      ⌜outcome = Build_ReadInputOutcome 0x2001a000⌝ ∗
      ⌜bv_unsigned sizeWord = Z.of_nat (length (readInputBytes args))⌝ ∗
      ⌜bv_unsigned savedWord = readSavedReturnAddress args⌝ ∗
      reg_col zesu_ram_sys_regs ∗
      "x1" ↦ᵣ RVal_Bits (BV 64 0x14ccc) ∗
      "x5" ↦ᵣ RVal_Bits (BV 64 0x2401a0b8) ∗
      "x6" ↦ᵣ RVal_Bits sizeWord ∗
      "x10" ↦ᵣ RVal_Bits bufferSlot ∗
      "x11" ↦ᵣ RVal_Bits sizeSlot ∗
      bv_unsigned (bufferSlot + (BV 64 0)) ↦ₘ (BV 64 0x2001a000) ∗
      bv_unsigned (sizeSlot + (BV 64 0)) ↦ₘ sizeWord ∗
      bv_unsigned (readInputIoPointer + (BV 64 0)) ↦ₘ sizeWord ∗
      0x2001a000 ↦ₘ∗ readInputMemory (readInputBytes args) ∗
      readSavedFrameAddress args ↦ₘ savedWord ∗ True)%I
|}.

Definition readInputAllows
    (_ : ReadInputArgs) (outcome : ReadInputOutcome) : Prop :=
  readInputAddress outcome = 0x2001a000.

Theorem read_input_state_correct `{!islaG Sigma} `{!threadG} :
  ⊢ IslarisContractSpec 0x10140 0x14ccc
    readInputAllows read_input_resources.
Proof.
  rewrite /IslarisContractSpec /read_input_resources /=.
  iStartProof.
  iIntros "(Hi1&Hi2&Hi3&Hi4&Hi5&Hi6&Hi7&Hi8)" (args).
  repeat lazymatch goal with
  | |- _ ⊢ WPasm tnil => fail 1
  | _ => zesu_liAStep
  end.
  liShow.
  iExists (Build_ReadInputOutcome 0x2001a000, tt)ₗ.
  red_li_prod. iSplit; first done.
  iExists bufferSlot, sizeSlot, sizeWord, savedWord.
  unshelve (repeat zesu_liAStep; liShow).
  Unshelve. all: prepare_sidecond.
  all: try (apply Z.le_ge;
    change (0x20000000 <= bv_unsigned sizeSlot)%Z;
    clear -H0 H1 H3 H9; lia).
  all: zesu_finish.
Qed.

Definition readInputControlFlow : list (Z * Z) := [
  (0x10140, 0x10144); (0x10144, 0x10148);
  (0x10148, 0x1014c); (0x1014c, 0x10150);
  (0x10150, 0x10154); (0x10154, 0x10158);
  (0x10158, 0x1015c); (0x1015c, 0x14ccc)
].

Definition readInputInstructionStep (fromPc toPc : Z) : Prop :=
  List.In (fromPc, toPc) readInputControlFlow.

Definition readInputModel :
    IslarisContractModel ReadInputArgs ReadInputOutcome := {|
  islarisContractAllows := readInputAllows;
  islarisContractStep := readInputInstructionStep;
  islarisContractResources := fun Sigma HG HT =>
    @read_input_resources Sigma HG HT
|}.

Definition readInputCorrectness : Prop :=
  IslarisContractCorrect 0x10140 0x14ccc readInputModel.

Definition readInputPath : list Z := [
  0x10140; 0x10144; 0x10148; 0x1014c; 0x10150;
  0x10154; 0x10158; 0x1015c; 0x14ccc
].

Lemma readInputTermination :
  InstructionPathCertificate readInputInstructionStep
    (PcInRanges readInputExecutionPcRanges)
    (PcInList readInputExitPcs) 0x10140 8.
Proof.
  exists readInputPath. split; first reflexivity. split.
  - unfold readInputPath.
    solve_instruction_path ltac:(
      cbn [readInputInstructionStep readInputControlFlow];
      repeat first [left; reflexivity | right]).
  - split.
    + apply Forall_forall. intros pc Hpc.
      unfold PcInRanges. eexists 0x10140, 0x10190. split.
      * cbn. auto.
      * unfold readInputPath in Hpc. cbn in Hpc.
        apply elem_of_list_In in Hpc. cbn in Hpc. lia.
    + split.
      * eexists 0x14ccc. split; [reflexivity | cbn; auto].
      * split; [reflexivity | lia].
Qed.

Theorem level1ReadInput :
  exists bound : nat, Nat.lt bound level1ContractFuel /\
    NativeContractAssumption readInputCorrectness
      readInputInstructionStep
      (PcInRanges readInputExecutionPcRanges)
      (PcInList readInputExitPcs)
      ZesuSsz.Generated.Level1.readInputEntry bound.
Proof.
  exists 8%nat. split.
  - unfold level1ContractFuel.
    pose proof (Nat.pow_gt_lin_r 2 160 ltac:(lia)) as Hbound. lia.
  - apply nativeContractBridge.
    + intros Sigma HG HT. apply read_input_state_correct.
    + exact readInputTermination.
Qed.
