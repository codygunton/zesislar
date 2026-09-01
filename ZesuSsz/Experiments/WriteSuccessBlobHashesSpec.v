From Coq Require Import Lists.List ZArith.ZArith.
Require Import isla.riscv64.riscv64.
From IslaTraces.write_success_blocks Require Import
  Index HintsHashesLoop HintsBlobHashesLoop HintsStorageKeysLoop.
Require Import ZesuSsz.Contracts.IslarisMachine.
Require Import ZesuSsz.Contracts.IslarisCode.
Require Import ZesuSsz.Experiments.WriteSuccess.
Require Import ZesuSsz.Experiments.WriteSuccessCalls.

Import ListNotations.

Local Remove Hints subsume_instr_pre'_inst : typeclass_instances.
Local Existing Instance subsume_instr_pre_wand_inst | 1.
Require Import ZesuSsz.Experiments.WriteSuccessLoopCommon.
#[local] Hint Extern 7
  (FindInContext (FindInstrKind ?address ?later) FICSyntactic) =>
  let reduced := eval vm_compute in address in
  first [ constr_eq address reduced; fail 1
        | change (FindInContext (FindInstrKind reduced later) FICSyntactic);
          typeclasses eauto ] : typeclass_instances.

Fixpoint writeSuccessBlobHashesEvents (sp : bv 64) (count : nat)
    (tail : spec) : spec :=
  match count with
  | O => tail
  | S count =>
      writeOutputEvents (sp + BV 64 1680)%bv (BV 64 32)
        (writeSuccessBlobHashesEvents sp count tail)
  end.

Definition writeSuccessBlobHashesOtherRegisters : list string :=
  ["x1"; "x3"; "x4"; "x5"; "x6"; "x7"; "x8"; "x9";
   "x10"; "x11"; "x12"; "x13"; "x14"; "x15"; "x16"; "x17";
   "x18"; "x20"; "x21"; "x23"; "x24"; "x25"; "x26"; "x27";
   "x28"; "x29"; "x30"; "x31"].

Definition writeSuccessBlobHashesOtherRegShapes :
    list (reg_kind * valu_shape) :=
  (fun register => (KindReg register, BitsShape 64))
    <$> writeSuccessBlobHashesOtherRegisters.

Definition writeSuccessBlobHashesBodyOtherRegisters : list string :=
  ["x1"; "x3"; "x4"; "x5"; "x6"; "x7"; "x8"; "x9";
   "x10"; "x11"; "x12"; "x13"; "x14"; "x15"; "x16"; "x17";
   "x18"; "x20"; "x21"; "x22"; "x23"; "x24"; "x25"; "x26";
   "x28"; "x29"; "x30"; "x31"].

Definition writeSuccessBlobHashesBodyOtherRegShapes :
    list (reg_kind * valu_shape) :=
  (fun register => (KindReg register, BitsShape 64))
    <$> writeSuccessBlobHashesBodyOtherRegisters.

Definition writeSuccessBlobHashesScratch `{!islaG Sigma}
    (sp : bv 64) : iProp Sigma :=
  (∃ word0 word1 word2 word3 : bv 64,
    (bv_unsigned sp + 1680) ↦ₘ word0 ∗
    (bv_unsigned sp + 1688) ↦ₘ word1 ∗
    (bv_unsigned sp + 1696) ↦ₘ word2 ∗
    (bv_unsigned sp + 1704) ↦ₘ word3 ∗ True)%I.

Global Instance : LithiumUnfold (@writeSuccessBlobHashesScratch) := I.

Definition writeSuccessBlobHashesLoopExit `{!islaG Sigma} `{!threadG}
    (sp : bv 64) (base : Z) (total : nat) (bytes : list (bv 8))
    (tail : spec) (P : iProp Sigma) : iProp Sigma :=
  (∃ pointer : bv 64,
    reg_col zesu_ram_sys_regs ∗
    reg_col writeSuccessBlobHashesOtherRegShapes ∗
    "x2" ↦ᵣ RVal_Bits sp ∗ "x19" ↦ᵣ RVal_Bits pointer ∗
    "x22" ↦ᵣ RVal_Bits (BV 64 0) ∗
    base ↦ₘ∗ bytes ∗ writeSuccessBlobHashesScratch sp ∗
    mmio_range 0x2401a0c0 16 ∗ spec_trace tail ∗ P ∗
    ⌜bv_unsigned pointer = (base + 32 * Z.of_nat total)%Z⌝ ∗ True)%I.

Global Instance : LithiumUnfold (@writeSuccessBlobHashesLoopExit) := I.

Definition writeSuccessBlobHashesLoopSpec `{!islaG Sigma} `{!threadG}
    (P : iProp Sigma) : iProp Sigma :=
  (∃ (sp pointer : bv 64) (base : Z)
      (total processed remaining : nat) (bytes : list (bv 8))
      (tail : spec),
    reg_col zesu_ram_sys_regs ∗
    reg_col writeSuccessBlobHashesOtherRegShapes ∗
    "x2" ↦ᵣ RVal_Bits sp ∗
    "x19" ↦ᵣ RVal_Bits pointer ∗
    "x22" ↦ᵣ RVal_Bits (Z_to_bv 64 (Z.of_nat (S remaining))) ∗
    base ↦ₘ∗ bytes ∗ writeSuccessBlobHashesScratch sp ∗
    mmio_range 0x2401a0c0 16 ∗
    spec_trace (writeSuccessBlobHashesEvents sp (S remaining) tail) ∗ P ∗
    writeSuccessFixedWidthArrayInvariant
      sp pointer base total processed remaining bytes ∗
    instr_pre 0x15564
      (writeSuccessBlobHashesLoopExit sp base total bytes tail P) ∗ True)%I.

Global Instance : LithiumUnfold (@writeSuccessBlobHashesLoopSpec) := I.

Definition writeSuccessBlobHashesBodySpec `{!islaG Sigma} `{!threadG}
    (P : iProp Sigma) : iProp Sigma :=
  (∃ (sp pointer : bv 64) (base : Z)
      (total processed remaining : nat) (bytes : list (bv 8))
      (tail : spec),
    reg_col zesu_ram_sys_regs ∗
    reg_col writeSuccessBlobHashesBodyOtherRegShapes ∗
    "x2" ↦ᵣ RVal_Bits sp ∗
    "x19" ↦ᵣ RVal_Bits pointer ∗
    "x27" ↦ᵣ RVal_Bits (Z_to_bv 64 (Z.of_nat (S remaining))) ∗
    base ↦ₘ∗ bytes ∗ writeSuccessBlobHashesScratch sp ∗
    mmio_range 0x2401a0c0 16 ∗
    spec_trace (writeSuccessBlobHashesEvents sp (S remaining) tail) ∗ P ∗
    writeSuccessFixedWidthArrayInvariant
      sp pointer base total processed remaining bytes ∗
    instr_pre 0x15564
      (writeSuccessBlobHashesLoopExit sp base total bytes tail P) ∗ True)%I.

Global Instance : LithiumUnfold (@writeSuccessBlobHashesBodySpec) := I.

Definition writeSuccessBlobHashesTailSpec `{!islaG Sigma} `{!threadG}
    (P : iProp Sigma) : iProp Sigma :=
  (∃ (sp pointer : bv 64) (base : Z)
      (total processed remaining : nat) (bytes : list (bv 8))
      (tail : spec),
    reg_col zesu_ram_sys_regs ∗
    reg_col writeSuccessBlobHashesBodyOtherRegShapes ∗
    "x2" ↦ᵣ RVal_Bits sp ∗
    "x19" ↦ᵣ RVal_Bits pointer ∗
    "x27" ↦ᵣ RVal_Bits (Z_to_bv 64 (Z.of_nat (S remaining))) ∗
    base ↦ₘ∗ bytes ∗ writeSuccessBlobHashesScratch sp ∗
    mmio_range 0x2401a0c0 16 ∗
    spec_trace (writeSuccessBlobHashesEvents sp remaining tail) ∗ P ∗
    writeSuccessFixedWidthArrayInvariant
      sp pointer base total processed remaining bytes ∗
    instr_pre 0x15564
      (writeSuccessBlobHashesLoopExit sp base total bytes tail P) ∗ True)%I.

Global Instance : LithiumUnfold (@writeSuccessBlobHashesTailSpec) := I.

Ltac close_write_success_blob_bad_address Hbad :=
  lazymatch goal with
  | [ Hptr : bv_unsigned ?pointer = _ |- _ ] =>
      exfalso;
      assert (536870912 <= bv_unsigned pointer)%Z
        as HpointerLower by (rewrite Hptr; nia);
      assert (bv_unsigned pointer + 32 < 1073741824)%Z
        as HpointerUpper by (rewrite Hptr; nia);
      assert (0 <= bv_unsigned pointer + 32 < 18446744073709551616)%Z
        as HpointerRange by (rewrite Hptr; nia);
      bv_simplify_arith Hbad;
      clear - Hbad HpointerLower HpointerUpper HpointerRange;
      bv_solve
  end.

Ltac close_write_success_blob_address_branch :=
  lazymatch goal with
  | [ Hbad : ~ bv_signed (BV 128 33554432) <= _ |- _ ] =>
      close_write_success_blob_bad_address Hbad
  | [ Hbad : _ <= bv_signed (BV 128 34340864) |- _ ] =>
      close_write_success_blob_bad_address Hbad
  | [ Hbad : @eq (bv 64) (BV 64 1073745920) _ |- _ ] =>
      close_write_success_blob_bad_address Hbad
  | [ Hbad : @eq (bv 64) _ (BV 64 1073745920) |- _ ] =>
      close_write_success_blob_bad_address Hbad
  | [ Hbad : @eq (bv 64) (BV 64 1073745924) _ |- _ ] =>
      close_write_success_blob_bad_address Hbad
  | [ Hbad : @eq (bv 64) _ (BV 64 1073745924) |- _ ] =>
      close_write_success_blob_bad_address Hbad
  | [ Hbad : ~ bv_signed (BV 128 536870912) <= _ |- _ ] =>
      close_write_success_blob_bad_address Hbad
  | [ Hbad : ~ _ <= bv_signed (BV 128 1073741824) |- _ ] =>
      close_write_success_blob_bad_address Hbad
  end.

Ltac run_write_success_blob_chunk boundary :=
  lazymatch goal with
  | |- instr_body boundary _ => idtac
  | |- environments.envs_entails _
      (∃ _ : spec *ₗ list (bv 8) *ₗ nat *ₗ nat *ₗ Z *ₗ (), _)%I => idtac
  | |- environments.envs_entails _
      (∃ _ : spec *ₗ list (bv 8) *ₗ nat *ₗ nat *ₗ nat *ₗ Z *ₗ (), _)%I =>
      idtac
  | |- environments.envs_entails _ (⌜_⌝)%I =>
      prepare_sidecond;
      run_write_success_blob_chunk boundary
  | _ =>
      first
        [ progress unfold LET_ID
        | progress unfold TRACE_LET
        | progress unLET
        | liAStep;
          try close_infeasible_bv_branches;
          try unLET;
          try close_write_success_blob_address_branch
        | solve [exfalso; nia]
        | apply bv_eq; rewrite bv_and_unsigned; assumption
        | bv_solve
        | lia ];
      run_write_success_blob_chunk boundary
  end.

Ltac prove_write_success_blob_segment boundary :=
  move => *;
  iStartProof;
  iIntros "_ #Hlookup #Hcode Hnext";
  iEval (unfold IslaTraces.write_success_blocks.Index.spec_instr_resources)
    in "Hcode";
  run_write_success_blob_chunk boundary.
