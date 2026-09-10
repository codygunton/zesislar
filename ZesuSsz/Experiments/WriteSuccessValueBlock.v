From Coq Require Import Lists.List ZArith.ZArith.
Require Import isla.riscv64.riscv64.
From IslaTraces.write_success_blocks Require Import Index HintsValueBlock.
Require Import ZesuSsz.Contracts.IslarisMachine.
Require Import ZesuSsz.Contracts.IslarisCode.
Require Import ZesuSsz.Experiments.WriteSuccess.
Require Import ZesuSsz.Experiments.WriteSuccessCallAbi.
Require Import ZesuSsz.Experiments.WriteSuccessCalls.
Require Import ZesuSsz.Experiments.WriteSuccessEncoderCalls.
Require Import ZesuSsz.Experiments.WriteSuccessHeaderBlock.
Require Import ZesuSsz.Experiments.WriteSuccessHeaderSpec.

Import ListNotations.

Local Remove Hints subsume_instr_pre'_inst : typeclass_instances.
Local Existing Instance subsume_instr_pre_wand_inst | 1.

Definition writeSuccessValueWord (values : list (bv 64)) (index : nat) :
    bv 64 := default (BV 64 0) (values !! index).

Definition writeSuccessValueEvents (sp : bv 64) (values : list (bv 64))
    (tail : spec) : spec :=
  writeOutputEvents (sp - 16)%bv (BV 64 8)
    (writeOutputEvents (sp - 16)%bv (BV 64 8)
      (writeOutputEvents (sp - 16)%bv (BV 64 8)
        (writeOutputEvents (sp - 16)%bv (BV 64 8)
          (writeOutputEvents (sp - 48)%bv (BV 64 8)
            (writeOutputEvents (writeSuccessValueWord values 4)
              (writeSuccessValueWord values 5)
              (writeOutputEvents (sp - 16)%bv (BV 64 8)
                (writeOutputEvents (sp + 1588)%bv (BV 64 32)
                (writeOutputEvents (sp - 16)%bv (BV 64 8) tail)))))))).

Definition writeSuccessValueRegisters : list string :=
  ["x1"; "x3"; "x4"; "x5"; "x6"; "x7"; "x8"; "x9";
   "x12"; "x13"; "x14"; "x15"; "x16"; "x17";
   "x18"; "x19"; "x20"; "x21"; "x22"; "x23"; "x24"; "x25";
   "x26"; "x27"; "x28"; "x29"; "x30"; "x31"].

Definition writeSuccessValueRegShapes : list (reg_kind * valu_shape) :=
  (fun register => (KindReg register, BitsShape 64))
    <$> writeSuccessValueRegisters.

Definition writeSuccessValuePost `{!islaG Sigma} `{!threadG}
    (sp : bv 64) (values : list (bv 64)) (payload : list (bv 8))
    (tail : spec) (P : iProp Sigma) : iProp Sigma :=
  (reg_col zesu_ram_sys_regs ∗
   reg_col writeSuccessValueRegShapes ∗
   "x2" ↦ᵣ RVal_Bits sp ∗
   "x10" ↦ᵣ RVal_Bits (default (BV 64 0) (values !! 8%nat)) ∗
   "x11" ↦ᵣ RVal_Bits (BV 64 0) ∗
   (bv_unsigned sp - 48) ↦ₘ? 48 ∗
   (bv_unsigned sp + 1032) ↦ₘ∗ values ∗
   bv_unsigned (writeSuccessValueWord values 4) ↦ₘ∗ payload ∗
   (bv_unsigned sp + 104) ↦ₘ default (BV 64 0) (values !! 7%nat) ∗
   (bv_unsigned sp + 112) ↦ₘ default (BV 64 0) (values !! 8%nat) ∗
   mmio_range 0x2401a0c0 16 ∗ spec_trace tail ∗ P ∗ True)%I.

Definition writeSuccessValueSpec `{!islaG Sigma} `{!threadG}
    (P : iProp Sigma) : iProp Sigma :=
  (∃ (sp : bv 64) (values : list (bv 64)) (payload : list (bv 8))
      (tail : spec),
    reg_col zesu_ram_sys_regs ∗
    reg_col writeSuccessHeaderRegShapes ∗
    "x2" ↦ᵣ RVal_Bits sp ∗
    (bv_unsigned sp - 48) ↦ₘ? 48 ∗
    (bv_unsigned sp + 104) ↦ₘ? 16 ∗
    (bv_unsigned sp + 1032) ↦ₘ∗ values ∗
    bv_unsigned (writeSuccessValueWord values 4) ↦ₘ∗ payload ∗
    mmio_range 0x2401a0c0 16 ∗
    spec_trace (writeSuccessValueEvents sp values tail) ∗
    ⌜length values = 74%nat⌝ ∗
    ⌜bv_unsigned (writeSuccessValueWord values 5) = length payload⌝ ∗
    ⌜bv_unsigned sp `mod` 16 = 0⌝ ∗
    ⌜bv_unsigned sp `mod` 8 = 0⌝ ∗
    ⌜0x20000000 <= bv_unsigned sp - 48⌝ ∗
    ⌜bv_unsigned sp + 1896 < 0x40000000⌝ ∗
    P ∗ instr_pre 0x14f04
      (writeSuccessValuePost sp values payload tail P))%I.

Local Instance : LithiumUnfold (@writeSuccessValueSpec) := I.
Local Instance : LithiumUnfold (@writeSuccessValuePost) := I.

#[local] Hint Rewrite Z_to_bv_add Z_to_bv_unsigned :
  lithium_rewrite isla_coq_rewrite.

#[local] Hint Extern 7
  (FindInContext (FindInstrKind ?address ?later) FICSyntactic) =>
  let reduced := eval vm_compute in address in
  first [ constr_eq address reduced; fail 1
        | change (FindInContext (FindInstrKind reduced later) FICSyntactic);
          typeclasses eauto ] : typeclass_instances.

Ltac run_write_success_values :=
  lazymatch goal with
  | |- instr_body 0x14f04 _ => idtac
  | _ =>
      first
        [ progress unLET
        | progress iEval (unfold zesuWriteOutputCallSpec, zesu_c_call)
        | progress iEval (unfold zesuEncoderIntCallSpec)
        | progress iEval (unfold zesuEncoderBytesCallSpec, zesu_c_call)
        | liAStep
        | progress prepare_sidecond
        | reflexivity
        | vm_compute
        | bv_solve
        | lia ];
      run_write_success_values
  end.

Ltac run_write_success_value_returns :=
  lazymatch goal with
  | |- environments.envs_entails _ ((_ -∗ _) ∗ True) =>
      iSplit; [|done];
      liARun;
      run_write_success_value_returns
  | |- environments.envs_entails _
      (subsume
        (instr ?address
          (IslaTraces.write_success_blocks.Index.lookup ?address)) _ _) =>
      iEval (vm_compute [IslaTraces.write_success_blocks.Index.lookup]);
      iApply subsume_instr_some_pre;
      run_write_success_value_returns
  | _ => idtac
  end.

Lemma write_success_value_block `{!islaG Sigma} `{!threadG}
    (P : iProp Sigma) :
  instr_lookup_resources IslaTraces.write_success_blocks.Index.lookup -∗
  IslaTraces.write_success_blocks.Index.spec_instr_resources -∗
  □ instr_pre 0x10190 zesuWriteOutputCallSpec -∗
  □ instr_pre 0x15d10 zesuEncoderIntCallSpec -∗
  □ instr_pre 0x15c6c zesuEncoderBytesCallSpec -∗
  instr_body 0x14e88 (writeSuccessValueSpec P).
Proof.
  move => *.
  iStartProof.
  iIntros "_ #Hlookup #Hcode #Houtput #Hint #Hbytes".
  iEval (unfold IslaTraces.write_success_blocks.Index.spec_instr_resources)
    in "Hcode".
  liARun.
  Unshelve.
  all: try prepare_sidecond.
  all: try assumption.
  all: try (cbn; rewrite ?length_take ?length_drop; lia).
  all: try bv_solve.
  all: try lia.
  all: try iFrame.
  Unshelve.
  all: try iFrame.
  all: try prepare_sidecond.
  all: try assumption.
  all: try bv_solve.
  all: try lia.
  all: lazymatch goal with |- ?G => fail "side condition" G end.
  Unshelve.
  all: try run_write_success_values.
  Unshelve.
  all: try prepare_sidecond.
  all: try assumption.
  all: try bv_solve.
  all: try lia.
  all: try iFrame.
  Unshelve.
  all: try iEval (unfold LET_ID).
  run_write_success_value_returns.
  Unshelve.
  all: try prepare_sidecond.
  all: try assumption.
  all: try (cbn; rewrite ?length_take ?length_drop; lia).
  all: try bv_solve.
  all: try lia.
  all: try iFrame.
  Unshelve.
  all: try prepare_sidecond.
  all: try assumption.
  all: try (cbn; rewrite ?length_take ?length_drop; lia).
  all: try bv_solve.
  all: try lia.
  all: try iFrame.
  all: lazymatch goal with |- ?G => fail "side condition" G end.
  Unshelve.
  iExists
    (writeOutputEvents (sp - 16)%bv (BV 64 8)
       (writeOutputEvents (sp + 1588)%bv (BV 64 32)
          (writeOutputEvents (sp - 16)%bv (BV 64 8) tail)),
     payload, tt)ₗ.
  liARun.
  Unshelve.
  all: try prepare_sidecond.
  all: try assumption.
  all: try (cbn [writeSuccessValueWord]; lia).
  all: try bv_solve.
  all: try lia.
  all: try iFrame.
  Unshelve.
  all: try iEval (unfold LET_ID).
  run_write_success_value_returns.
  Unshelve.
  all: try prepare_sidecond.
  all: try assumption.
  all: try (cbn [writeSuccessValueWord]; lia).
  all: try bv_solve.
  all: try lia.
  all: try iFrame.
  Unshelve.
  run_write_success_value_returns.
  iExists tt.
  iSplit; [|done].
  iIntros "(HreturnedSys & HreturnedX1 & HreturnedX2 & HreturnedX5 & HreturnedX10 & HreturnedX11 & HreturnedScratch & HreturnedMmio & HreturnedTrace & _)".
  iIntros "HreturnedPC".
  do 225 liAStep.
  unLET.
  unfold LET_ID.
  iEval (unfold zesuWriteOutputCallSpec, zesu_c_call).
  liARun.
  run_write_success_value_returns.
  iExists tt.
  iSplit; [|done].
  iIntros "(? & ? & ? & ? & ? & ? & ? & ? & ? & _)".
  iIntros "?".
  iEval (unfold writeSuccessValueWord).
  repeat liAStep.
  Unshelve.
  all: try prepare_sidecond.
  all: try assumption.
  all: try bv_solve.
  all: try lia.
  all: try iFrame.
Qed.
