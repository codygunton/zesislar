From Coq Require Import Lists.List ZArith.ZArith.
Require Import isla.riscv64.riscv64.
From IslaTraces.write_success_blocks Require Import
  Index HintsHashesLoop HintsBlobHashesLoop.
Require Import ZesuSsz.Contracts.IslarisMachine.
Require Import ZesuSsz.Contracts.IslarisCode.
Require Import ZesuSsz.Experiments.WriteSuccess.
Require Import ZesuSsz.Experiments.WriteSuccessCalls.

Import ListNotations.

Local Remove Hints subsume_instr_pre'_inst : typeclass_instances.
Local Existing Instance subsume_instr_pre_wand_inst | 1.

Lemma bv_unsigned_add_no_wrap_64 (left right : bv 64) :
  (bv_unsigned left + bv_unsigned right < 2 ^ 64)%Z ->
  bv_unsigned (left + right)%bv = bv_unsigned left + bv_unsigned right.
Proof.
  move => Hsum. rewrite bv_add_unsigned.
  apply bv_wrap_small.
  pose proof (bv_unsigned_in_range 64 left).
  pose proof (bv_unsigned_in_range 64 right).
  unfold bv_modulus in *. cbn in *. lia.
Qed.

Fixpoint writeSuccessHashesEvents (sp : bv 64) (count : nat)
    (tail : spec) : spec :=
  match count with
  | O => tail
  | S count =>
      writeOutputEvents (sp + BV 64 1744)%bv (BV 64 32)
        (writeSuccessHashesEvents sp count tail)
  end.

Definition writeSuccessHashesOtherRegisters : list string :=
  ["x1"; "x3"; "x4"; "x5"; "x6"; "x7";
   "x10"; "x11"; "x12"; "x13"; "x14"; "x15"; "x16"; "x17";
   "x18"; "x19"; "x20"; "x21"; "x22"; "x23"; "x24"; "x25";
   "x26"; "x27"; "x28"; "x29"; "x30"; "x31"].

Definition writeSuccessHashesOtherRegShapes : list (reg_kind * valu_shape) :=
  (fun register => (KindReg register, BitsShape 64))
    <$> writeSuccessHashesOtherRegisters.

Definition writeSuccessHashesScratch `{!islaG Sigma}
    (sp : bv 64) : iProp Sigma :=
  (∃ word0 word1 word2 word3 : bv 64,
    (bv_unsigned sp + 1744) ↦ₘ word0 ∗
    (bv_unsigned sp + 1752) ↦ₘ word1 ∗
    (bv_unsigned sp + 1760) ↦ₘ word2 ∗
    (bv_unsigned sp + 1768) ↦ₘ word3 ∗ True)%I.

Global Instance : LithiumUnfold (@writeSuccessHashesScratch) := I.

Definition writeSuccessHashesLoopExit `{!islaG Sigma} `{!threadG}
    (sp : bv 64) (base : Z) (total : nat) (bytes : list (bv 8))
    (tail : spec) (P : iProp Sigma) : iProp Sigma :=
  (∃ pointer : bv 64,
    reg_col zesu_ram_sys_regs ∗
    reg_col writeSuccessHashesOtherRegShapes ∗
    "x2" ↦ᵣ RVal_Bits sp ∗ "x8" ↦ᵣ RVal_Bits (BV 64 0) ∗
    "x9" ↦ᵣ RVal_Bits pointer ∗
    base ↦ₘ∗ bytes ∗ writeSuccessHashesScratch sp ∗
    mmio_range 0x2401a0c0 16 ∗ spec_trace tail ∗ P ∗
    ⌜bv_unsigned pointer = (base + 32 * Z.of_nat total)%Z⌝ ∗ True)%I.

Global Instance : LithiumUnfold (@writeSuccessHashesLoopExit) := I.

Definition writeSuccessHashesLoopSpec `{!islaG Sigma} `{!threadG}
    (P : iProp Sigma) : iProp Sigma :=
  (∃ (sp pointer : bv 64) (base : Z)
      (total processed remaining : nat) (bytes : list (bv 8))
      (tail : spec),
    reg_col zesu_ram_sys_regs ∗
    reg_col writeSuccessHashesOtherRegShapes ∗
    "x2" ↦ᵣ RVal_Bits sp ∗
    "x8" ↦ᵣ RVal_Bits (Z_to_bv 64 (Z.of_nat (S remaining))) ∗
    "x9" ↦ᵣ RVal_Bits pointer ∗
    base ↦ₘ∗ bytes ∗ writeSuccessHashesScratch sp ∗
    mmio_range 0x2401a0c0 16 ∗
    spec_trace (writeSuccessHashesEvents sp (S remaining) tail) ∗ P ∗
    ⌜total = (processed + S remaining)%nat⌝ ∗
    ⌜length bytes = (32 * total)%nat⌝ ∗
    ⌜bv_unsigned pointer = (base + 32 * Z.of_nat processed)%Z⌝ ∗
    ⌜(S remaining < 2 ^ 64)%nat⌝ ∗
    ⌜bv_unsigned sp `mod` 16 = 0⌝ ∗
    ⌜(0x20000000 <= bv_unsigned sp)%Z⌝ ∗
    ⌜(bv_unsigned sp + 1896 < 0x40000000)%Z⌝ ∗
    ⌜(0x20000000 <= base)%Z⌝ ∗
    ⌜(base + Z.of_nat (length bytes) < 0x40000000)%Z⌝ ∗
    instr_pre 0x158e0
      (writeSuccessHashesLoopExit sp base total bytes tail P) ∗ True)%I.

Global Instance : LithiumUnfold (@writeSuccessHashesLoopSpec) := I.

#[local] Hint Extern 7
  (FindInContext (FindInstrKind ?address ?later) FICSyntactic) =>
  let reduced := eval vm_compute in address in
  first [ constr_eq address reduced; fail 1
        | change (FindInContext (FindInstrKind reduced later) FICSyntactic);
          typeclasses eauto ] : typeclass_instances.

Lemma write_success_hashes_word3 `{!islaG Sigma} `{!threadG}
    (P : iProp Sigma) :
  instr_lookup_resources IslaTraces.write_success_blocks.Index.lookup -∗
  IslaTraces.write_success_blocks.Index.spec_instr_resources -∗
  instr_body 0x157b0 (writeSuccessHashesLoopSpec P) -∗
  instr_body 0x15754 (writeSuccessHashesLoopSpec P).
Proof.
  move => *.
  iStartProof.
  iIntros "_ #Hlookup #Hcode Hnext".
  iEval (unfold IslaTraces.write_success_blocks.Index.spec_instr_resources)
    in "Hcode".
  do 2000 liAStep.
  liARun.
  iExists
    (tail, bytes, processed, (processed + S remaining)%nat, base, tt)ₗ.
  liARun.
  Unshelve.
  all: prepare_sidecond.
  all: try (apply bv_eq; rewrite bv_and_unsigned; assumption).
  all: try (bv_simplify_arith H1; bv_solve).
Qed.

Lemma write_success_hashes_word2 `{!islaG Sigma} `{!threadG}
    (P : iProp Sigma) :
  instr_lookup_resources IslaTraces.write_success_blocks.Index.lookup -∗
  IslaTraces.write_success_blocks.Index.spec_instr_resources -∗
  instr_body 0x1580c (writeSuccessHashesLoopSpec P) -∗
  instr_body 0x157b0 (writeSuccessHashesLoopSpec P).
Proof.
  move => *.
  iStartProof.
  iIntros "_ #Hlookup #Hcode Hnext".
  iEval (unfold IslaTraces.write_success_blocks.Index.spec_instr_resources)
    in "Hcode".
  liARun.
  iExists
    (tail, bytes, processed, (processed + S remaining)%nat, base, tt)ₗ.
  liARun.
  Unshelve.
  all: prepare_sidecond.
  all: try (apply bv_eq; rewrite bv_and_unsigned; assumption).
  all: try (bv_simplify_arith H1; bv_solve).
Qed.

Lemma write_success_hashes_word1 `{!islaG Sigma} `{!threadG}
    (P : iProp Sigma) :
  instr_lookup_resources IslaTraces.write_success_blocks.Index.lookup -∗
  IslaTraces.write_success_blocks.Index.spec_instr_resources -∗
  instr_body 0x15868 (writeSuccessHashesLoopSpec P) -∗
  instr_body 0x1580c (writeSuccessHashesLoopSpec P).
Proof.
  move => *.
  iStartProof.
  iIntros "_ #Hlookup #Hcode Hnext".
  iEval (unfold IslaTraces.write_success_blocks.Index.spec_instr_resources)
    in "Hcode".
  liARun.
  iExists
    (tail, bytes, processed, (processed + S remaining)%nat, base, tt)ₗ.
  liARun.
  Unshelve.
  all: prepare_sidecond.
  all: try (apply bv_eq; rewrite bv_and_unsigned; assumption).
  all: try (bv_simplify_arith H1; bv_solve).
Qed.

Lemma write_success_hashes_word0 `{!islaG Sigma} `{!threadG}
    (P : iProp Sigma) :
  instr_lookup_resources IslaTraces.write_success_blocks.Index.lookup -∗
  IslaTraces.write_success_blocks.Index.spec_instr_resources -∗
  instr_body 0x158c4 (writeSuccessHashesLoopSpec P) -∗
  instr_body 0x15868 (writeSuccessHashesLoopSpec P).
Proof.
  move => *.
  iStartProof.
  iIntros "_ #Hlookup #Hcode Hnext".
  iEval (unfold IslaTraces.write_success_blocks.Index.spec_instr_resources)
    in "Hcode".
  liARun.
  iExists
    (tail, bytes, processed, (processed + S remaining)%nat, base, tt)ₗ.
  liARun.
  Unshelve.
  all: prepare_sidecond.
  all: try (apply bv_eq; rewrite bv_and_unsigned; assumption).
  all: try (bv_simplify_arith H1; bv_solve).
Qed.

Lemma write_success_hashes_tail `{!islaG Sigma} `{!threadG}
    (P : iProp Sigma) :
  instr_lookup_resources IslaTraces.write_success_blocks.Index.lookup -∗
  IslaTraces.write_success_blocks.Index.spec_instr_resources -∗
  □ instr_pre 0x10190 zesuWriteOutputCallSpec -∗
  □ instr_pre 0x15754 (writeSuccessHashesLoopSpec P) -∗
  instr_body 0x158c4 (writeSuccessHashesLoopSpec P).
Proof.
  move => *.
  iStartProof.
  iIntros "_ #Hlookup #Hcode #Houtput #Hloop".
  iEval (unfold IslaTraces.write_success_blocks.Index.spec_instr_resources)
    in "Hcode".
  liARun.
  destruct remaining as [|remaining'].
  - exfalso. apply H14. bv_solve.
  - iExists
      (tail, bytes, remaining', S processed,
       (processed + S (S remaining'))%nat, base,
       (pointer + BV 64 32)%bv, tt)ₗ.
    liARun.
  Unshelve.
  all: prepare_sidecond.
  all: try (apply bv_eq; rewrite bv_and_unsigned; assumption).
  all: try (bv_simplify_arith H1; bv_solve).
  all: try lia.
  all: try iFrame.
  all: have Hremaining : remaining = O by
    (bv_simplify_arith H14; bv_solve).
  all: subst remaining.
  all: cbn.
  all: try reflexivity.
  all: try (bv_simplify_arith H1; bv_solve).
Qed.

Lemma write_success_hashes_loop `{!islaG Sigma} `{!threadG}
    (P : iProp Sigma) :
  instr_lookup_resources IslaTraces.write_success_blocks.Index.lookup -∗
  IslaTraces.write_success_blocks.Index.spec_instr_resources -∗
  □ instr_pre 0x10190 zesuWriteOutputCallSpec -∗
  □ instr_pre 0x15754 (writeSuccessHashesLoopSpec P) -∗
  instr_body 0x15754 (writeSuccessHashesLoopSpec P).
Proof.
  iStartProof. iIntros "#Hlookup #Hcode #Houtput #Hloop".
  iApply (write_success_hashes_word3 P with "Hlookup Hcode").
  iApply (write_success_hashes_word2 P with "Hlookup Hcode").
  iApply (write_success_hashes_word1 P with "Hlookup Hcode").
  iApply (write_success_hashes_word0 P with "Hlookup Hcode").
  iApply (write_success_hashes_tail P with
    "Hlookup Hcode Houtput Hloop").
Qed.

Lemma write_success_hashes_loop_pre `{!islaG Sigma} `{!threadG}
    (P : iProp Sigma) :
  instr_lookup_resources IslaTraces.write_success_blocks.Index.lookup -∗
  IslaTraces.write_success_blocks.Index.spec_instr_resources -∗
  □ instr_pre 0x10190 zesuWriteOutputCallSpec -∗
  □ instr_pre 0x15754 (writeSuccessHashesLoopSpec P).
Proof.
  iStartProof. iIntros "#Hlookup #Hcode #Houtput".
  iLöb as "IH".
  iModIntro. iApply instr_pre_to_body. iNext.
  iApply (write_success_hashes_loop P with "Hlookup Hcode Houtput IH").
Qed.

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
    ⌜total = (processed + S remaining)%nat⌝ ∗
    ⌜length bytes = (32 * total)%nat⌝ ∗
    ⌜bv_unsigned pointer = (base + 32 * Z.of_nat processed)%Z⌝ ∗
    ⌜(S remaining < 2 ^ 64)%nat⌝ ∗
    ⌜bv_unsigned sp `mod` 16 = 0⌝ ∗
    ⌜(0x20000000 <= bv_unsigned sp)%Z⌝ ∗
    ⌜(bv_unsigned sp + 1896 < 0x40000000)%Z⌝ ∗
    ⌜(0x20000000 <= base)%Z⌝ ∗
    ⌜(base + Z.of_nat (length bytes) < 0x40000000)%Z⌝ ∗
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
    ⌜total = (processed + S remaining)%nat⌝ ∗
    ⌜length bytes = (32 * total)%nat⌝ ∗
    ⌜bv_unsigned pointer = (base + 32 * Z.of_nat processed)%Z⌝ ∗
    ⌜(S remaining < 2 ^ 64)%nat⌝ ∗
    ⌜bv_unsigned sp `mod` 16 = 0⌝ ∗
    ⌜(0x20000000 <= bv_unsigned sp)%Z⌝ ∗
    ⌜(bv_unsigned sp + 1896 < 0x40000000)%Z⌝ ∗
    ⌜(0x20000000 <= base)%Z⌝ ∗
    ⌜(base + Z.of_nat (length bytes) < 0x40000000)%Z⌝ ∗
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
    ⌜total = (processed + S remaining)%nat⌝ ∗
    ⌜length bytes = (32 * total)%nat⌝ ∗
    ⌜bv_unsigned pointer = (base + 32 * Z.of_nat processed)%Z⌝ ∗
    ⌜(S remaining < 2 ^ 64)%nat⌝ ∗
    ⌜bv_unsigned sp `mod` 16 = 0⌝ ∗
    ⌜(0x20000000 <= bv_unsigned sp)%Z⌝ ∗
    ⌜(bv_unsigned sp + 1896 < 0x40000000)%Z⌝ ∗
    ⌜(0x20000000 <= base)%Z⌝ ∗
    ⌜(base + Z.of_nat (length bytes) < 0x40000000)%Z⌝ ∗
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

Lemma write_success_blob_hashes_chunk0a `{!islaG Sigma} `{!threadG}
    (P : iProp Sigma) :
  instr_lookup_resources IslaTraces.write_success_blocks.Index.lookup -∗
  IslaTraces.write_success_blocks.Index.spec_instr_resources -∗
  instr_body 0x153dc (writeSuccessBlobHashesLoopSpec P) -∗
  instr_body 0x153d4 (writeSuccessBlobHashesLoopSpec P).
Proof.
  prove_write_success_blob_segment 0x153dc.
  liARun.
  iExists
    (tail, bytes, processed, (processed + S remaining)%nat, base, tt)ₗ.
  liARun.
  Unshelve.
  all: prepare_sidecond.
  all: try (apply bv_eq; rewrite bv_and_unsigned; assumption).
  all: try (bv_simplify_arith H1; bv_solve).
  Unshelve. all: try liARun.
Qed.

Lemma write_success_blob_hashes_chunk0b `{!islaG Sigma} `{!threadG}
    (P : iProp Sigma) :
  instr_lookup_resources IslaTraces.write_success_blocks.Index.lookup -∗
  IslaTraces.write_success_blocks.Index.spec_instr_resources -∗
  instr_body 0x153e4 (writeSuccessBlobHashesLoopSpec P) -∗
  instr_body 0x153dc (writeSuccessBlobHashesLoopSpec P).
Proof.
  prove_write_success_blob_segment 0x153e4.
  liARun.
  iExists
    (tail, bytes, processed, (processed + S remaining)%nat, base, tt)ₗ.
  liARun.
  Unshelve.
  all: prepare_sidecond.
  all: try (apply bv_eq; rewrite bv_and_unsigned; assumption).
  all: try (bv_simplify_arith H1; bv_solve).
  Unshelve. all: try liARun.
Qed.

Lemma write_success_blob_hashes_chunk0c `{!islaG Sigma} `{!threadG}
    (P : iProp Sigma) :
  instr_lookup_resources IslaTraces.write_success_blocks.Index.lookup -∗
  IslaTraces.write_success_blocks.Index.spec_instr_resources -∗
  instr_body 0x153ec (writeSuccessBlobHashesLoopSpec P) -∗
  instr_body 0x153e4 (writeSuccessBlobHashesLoopSpec P).
Proof.
  prove_write_success_blob_segment 0x153ec.
  liARun.
  iExists
    (tail, bytes, processed, (processed + S remaining)%nat, base, tt)ₗ.
  liARun.
  Unshelve.
  all: prepare_sidecond.
  all: try (apply bv_eq; rewrite bv_and_unsigned; assumption).
  all: try (bv_simplify_arith H1; bv_solve).
  Unshelve. all: try liARun.
Qed.

Lemma write_success_blob_hashes_chunk0d `{!islaG Sigma} `{!threadG}
    (P : iProp Sigma) :
  instr_lookup_resources IslaTraces.write_success_blocks.Index.lookup -∗
  IslaTraces.write_success_blocks.Index.spec_instr_resources -∗
  instr_body 0x153f4 (writeSuccessBlobHashesLoopSpec P) -∗
  instr_body 0x153ec (writeSuccessBlobHashesLoopSpec P).
Proof.
  prove_write_success_blob_segment 0x153f4.
  liARun.
  iExists
    (tail, bytes, processed, (processed + S remaining)%nat, base, tt)ₗ.
  liARun.
  Unshelve.
  all: prepare_sidecond.
  all: try (apply bv_eq; rewrite bv_and_unsigned; assumption).
  all: try (bv_simplify_arith H1; bv_solve).
  Unshelve. all: try liARun.
Qed.

Lemma write_success_blob_hashes_chunk0e `{!islaG Sigma} `{!threadG}
    (P : iProp Sigma) :
  instr_lookup_resources IslaTraces.write_success_blocks.Index.lookup -∗
  IslaTraces.write_success_blocks.Index.spec_instr_resources -∗
  instr_body 0x153fc (writeSuccessBlobHashesLoopSpec P) -∗
  instr_body 0x153f4 (writeSuccessBlobHashesLoopSpec P).
Proof.
  prove_write_success_blob_segment 0x153fc.
  liARun.
  iExists
    (tail, bytes, processed, (processed + S remaining)%nat, base, tt)ₗ.
  liARun.
  Unshelve.
  all: prepare_sidecond.
  all: try (apply bv_eq; rewrite bv_and_unsigned; assumption).
  all: try (bv_simplify_arith H1; bv_solve).
  Unshelve. all: try liARun.
Qed.

Lemma write_success_blob_hashes_chunk0f `{!islaG Sigma} `{!threadG}
    (P : iProp Sigma) :
  instr_lookup_resources IslaTraces.write_success_blocks.Index.lookup -∗
  IslaTraces.write_success_blocks.Index.spec_instr_resources -∗
  instr_body 0x15404 (writeSuccessBlobHashesLoopSpec P) -∗
  instr_body 0x153fc (writeSuccessBlobHashesLoopSpec P).
Proof.
  prove_write_success_blob_segment 0x15404.
  liARun.
  iExists
    (tail, bytes, processed, (processed + S remaining)%nat, base, tt)ₗ.
  liARun.
  Unshelve.
  all: prepare_sidecond.
  all: try (apply bv_eq; rewrite bv_and_unsigned; assumption).
  all: try (bv_simplify_arith H1; bv_solve).
  Unshelve. all: try liARun.
Qed.

Lemma write_success_blob_hashes_chunk0g `{!islaG Sigma} `{!threadG}
    (P : iProp Sigma) :
  instr_lookup_resources IslaTraces.write_success_blocks.Index.lookup -∗
  IslaTraces.write_success_blocks.Index.spec_instr_resources -∗
  instr_body 0x1540c (writeSuccessBlobHashesLoopSpec P) -∗
  instr_body 0x15404 (writeSuccessBlobHashesLoopSpec P).
Proof.
  prove_write_success_blob_segment 0x1540c.
  liARun.
  iExists
    (tail, bytes, processed, (processed + S remaining)%nat, base, tt)ₗ.
  liARun.
  Unshelve.
  all: prepare_sidecond.
  all: try (apply bv_eq; rewrite bv_and_unsigned; assumption).
  all: try (bv_simplify_arith H1; bv_solve).
  Unshelve. all: try liARun.
Qed.

Lemma write_success_blob_hashes_chunk0h `{!islaG Sigma} `{!threadG}
    (P : iProp Sigma) :
  instr_lookup_resources IslaTraces.write_success_blocks.Index.lookup -∗
  IslaTraces.write_success_blocks.Index.spec_instr_resources -∗
  instr_body 0x15414 (writeSuccessBlobHashesLoopSpec P) -∗
  instr_body 0x1540c (writeSuccessBlobHashesLoopSpec P).
Proof.
  prove_write_success_blob_segment 0x15414.
  liARun.
  iExists
    (tail, bytes, processed, (processed + S remaining)%nat, base, tt)ₗ.
  liARun.
  Unshelve.
  all: prepare_sidecond.
  all: try (apply bv_eq; rewrite bv_and_unsigned; assumption).
  all: try (bv_simplify_arith H1; bv_solve).
  Unshelve. all: try liARun.
Qed.

Lemma write_success_blob_hashes_chunk0i `{!islaG Sigma} `{!threadG}
    (P : iProp Sigma) :
  instr_lookup_resources IslaTraces.write_success_blocks.Index.lookup -∗
  IslaTraces.write_success_blocks.Index.spec_instr_resources -∗
  instr_body 0x1541c (writeSuccessBlobHashesLoopSpec P) -∗
  instr_body 0x15414 (writeSuccessBlobHashesLoopSpec P).
Proof.
  prove_write_success_blob_segment 0x1541c.
  liARun.
  iExists
    (tail, bytes, processed, (processed + S remaining)%nat, base, tt)ₗ.
  liARun.
  Unshelve.
  all: prepare_sidecond.
  all: try (apply bv_eq; rewrite bv_and_unsigned; assumption).
  all: try (bv_simplify_arith H1; bv_solve).
  Unshelve. all: try liARun.
Qed.

Lemma write_success_blob_hashes_chunk0j `{!islaG Sigma} `{!threadG}
    (P : iProp Sigma) :
  instr_lookup_resources IslaTraces.write_success_blocks.Index.lookup -∗
  IslaTraces.write_success_blocks.Index.spec_instr_resources -∗
  instr_body 0x15424 (writeSuccessBlobHashesLoopSpec P) -∗
  instr_body 0x1541c (writeSuccessBlobHashesLoopSpec P).
Proof.
  prove_write_success_blob_segment 0x15424.
  liARun.
  iExists
    (tail, bytes, processed, (processed + S remaining)%nat, base, tt)ₗ.
  liARun.
  Unshelve.
  all: prepare_sidecond.
  all: try (apply bv_eq; rewrite bv_and_unsigned; assumption).
  all: try (bv_simplify_arith H1; bv_solve).
  Unshelve. all: try liARun.
Qed.

Lemma write_success_blob_hashes_chunk0k `{!islaG Sigma} `{!threadG}
    (P : iProp Sigma) :
  instr_lookup_resources IslaTraces.write_success_blocks.Index.lookup -∗
  IslaTraces.write_success_blocks.Index.spec_instr_resources -∗
  instr_body 0x1542c (writeSuccessBlobHashesBodySpec P) -∗
  instr_body 0x15424 (writeSuccessBlobHashesLoopSpec P).
Proof.
  prove_write_success_blob_segment 0x1542c.
  liARun.
  iExists
    (tail, bytes, remaining, processed,
     (processed + S remaining)%nat, base, tt)ₗ.
  liARun.
  Unshelve.
  all: prepare_sidecond.
  all: try (apply bv_eq; rewrite bv_and_unsigned; assumption).
  all: try (bv_simplify_arith H1; bv_solve).
  Unshelve. all: try liARun.
Qed.

Lemma write_success_blob_hashes_chunk0l `{!islaG Sigma} `{!threadG}
    (P : iProp Sigma) :
  instr_lookup_resources IslaTraces.write_success_blocks.Index.lookup -∗
  IslaTraces.write_success_blocks.Index.spec_instr_resources -∗
  instr_body 0x15434 (writeSuccessBlobHashesBodySpec P) -∗
  instr_body 0x1542c (writeSuccessBlobHashesBodySpec P).
Proof.
  prove_write_success_blob_segment 0x15434.
  liARun.
  iExists
    (tail, bytes, processed, (processed + S remaining)%nat, base, tt)ₗ.
  liARun.
  Unshelve.
  all: prepare_sidecond.
  all: try (apply bv_eq; rewrite bv_and_unsigned; assumption).
  all: try (bv_simplify_arith H1; bv_solve).
  Unshelve. all: try liARun.
Qed.

Lemma write_success_blob_hashes_chunk0 `{!islaG Sigma} `{!threadG}
    (P : iProp Sigma) :
  instr_lookup_resources IslaTraces.write_success_blocks.Index.lookup -∗
  IslaTraces.write_success_blocks.Index.spec_instr_resources -∗
  instr_body 0x15434 (writeSuccessBlobHashesBodySpec P) -∗
  instr_body 0x153d4 (writeSuccessBlobHashesLoopSpec P).
Proof.
  iStartProof. iIntros "#Hlookup #Hcode Hnext".
  iApply (write_success_blob_hashes_chunk0a P with "Hlookup Hcode").
  iApply (write_success_blob_hashes_chunk0b P with "Hlookup Hcode").
  iApply (write_success_blob_hashes_chunk0c P with "Hlookup Hcode").
  iApply (write_success_blob_hashes_chunk0d P with "Hlookup Hcode").
  iApply (write_success_blob_hashes_chunk0e P with "Hlookup Hcode").
  iApply (write_success_blob_hashes_chunk0f P with "Hlookup Hcode").
  iApply (write_success_blob_hashes_chunk0g P with "Hlookup Hcode").
  iApply (write_success_blob_hashes_chunk0h P with "Hlookup Hcode").
  iApply (write_success_blob_hashes_chunk0i P with "Hlookup Hcode").
  iApply (write_success_blob_hashes_chunk0j P with "Hlookup Hcode").
  iApply (write_success_blob_hashes_chunk0k P with "Hlookup Hcode").
  iApply (write_success_blob_hashes_chunk0l P with "Hlookup Hcode").
  iExact "Hnext".
Qed.

Lemma write_success_blob_hashes_chunk1a `{!islaG Sigma} `{!threadG}
    (P : iProp Sigma) :
  instr_lookup_resources IslaTraces.write_success_blocks.Index.lookup -∗
  IslaTraces.write_success_blocks.Index.spec_instr_resources -∗
  instr_body 0x15454 (writeSuccessBlobHashesBodySpec P) -∗
  instr_body 0x15434 (writeSuccessBlobHashesBodySpec P).
Proof.
  prove_write_success_blob_segment 0x15454.
  liARun.
  iExists
    (tail, bytes, processed, (processed + S remaining)%nat, base, tt)ₗ.
  liARun.
  Unshelve.
  all: prepare_sidecond.
  all: try (apply bv_eq; rewrite bv_and_unsigned; assumption).
  all: try (bv_simplify_arith H1; bv_solve).
  Unshelve. all: try liARun.
Qed.

Lemma write_success_blob_hashes_chunk1b `{!islaG Sigma} `{!threadG}
    (P : iProp Sigma) :
  instr_lookup_resources IslaTraces.write_success_blocks.Index.lookup -∗
  IslaTraces.write_success_blocks.Index.spec_instr_resources -∗
  instr_body 0x1545c (writeSuccessBlobHashesBodySpec P) -∗
  instr_body 0x15454 (writeSuccessBlobHashesBodySpec P).
Proof.
  prove_write_success_blob_segment 0x1545c.
  liARun.
  iExists
    (tail, bytes, processed, (processed + S remaining)%nat, base, tt)ₗ.
  liARun.
  Unshelve.
  all: prepare_sidecond.
  all: try (apply bv_eq; rewrite bv_and_unsigned; assumption).
  all: try (bv_simplify_arith H1; bv_solve).
  Unshelve. all: try liARun.
Qed.

Lemma write_success_blob_hashes_chunk1c `{!islaG Sigma} `{!threadG}
    (P : iProp Sigma) :
  instr_lookup_resources IslaTraces.write_success_blocks.Index.lookup -∗
  IslaTraces.write_success_blocks.Index.spec_instr_resources -∗
  instr_body 0x15464 (writeSuccessBlobHashesBodySpec P) -∗
  instr_body 0x1545c (writeSuccessBlobHashesBodySpec P).
Proof.
  prove_write_success_blob_segment 0x15464.
  liARun.
  iExists
    (tail, bytes, processed, (processed + S remaining)%nat, base, tt)ₗ.
  liARun.
  Unshelve.
  all: prepare_sidecond.
  all: try (apply bv_eq; rewrite bv_and_unsigned; assumption).
  all: try (bv_simplify_arith H1; bv_solve).
  Unshelve. all: try liARun.
Qed.

Lemma write_success_blob_hashes_chunk1d `{!islaG Sigma} `{!threadG}
    (P : iProp Sigma) :
  instr_lookup_resources IslaTraces.write_success_blocks.Index.lookup -∗
  IslaTraces.write_success_blocks.Index.spec_instr_resources -∗
  instr_body 0x1548c (writeSuccessBlobHashesBodySpec P) -∗
  instr_body 0x15464 (writeSuccessBlobHashesBodySpec P).
Proof.
  prove_write_success_blob_segment 0x1548c.
  liARun.
  iExists
    (tail, bytes, processed, (processed + S remaining)%nat, base, tt)ₗ.
  liARun.
  Unshelve.
  all: prepare_sidecond.
  all: try (apply bv_eq; rewrite bv_and_unsigned; assumption).
  all: try (bv_simplify_arith H1; bv_solve).
  Unshelve. all: try liARun.
Qed.

Lemma write_success_blob_hashes_chunk1e `{!islaG Sigma} `{!threadG}
    (P : iProp Sigma) :
  instr_lookup_resources IslaTraces.write_success_blocks.Index.lookup -∗
  IslaTraces.write_success_blocks.Index.spec_instr_resources -∗
  instr_body 0x15494 (writeSuccessBlobHashesBodySpec P) -∗
  instr_body 0x1548c (writeSuccessBlobHashesBodySpec P).
Proof.
  prove_write_success_blob_segment 0x15494.
  liARun.
  iExists
    (tail, bytes, processed, (processed + S remaining)%nat, base, tt)ₗ.
  liARun.
  Unshelve.
  all: prepare_sidecond.
  all: try (apply bv_eq; rewrite bv_and_unsigned; assumption).
  all: try (bv_simplify_arith H1; bv_solve).
  Unshelve. all: try liARun.
Qed.

Lemma write_success_blob_hashes_chunk1 `{!islaG Sigma} `{!threadG}
    (P : iProp Sigma) :
  instr_lookup_resources IslaTraces.write_success_blocks.Index.lookup -∗
  IslaTraces.write_success_blocks.Index.spec_instr_resources -∗
  instr_body 0x15494 (writeSuccessBlobHashesBodySpec P) -∗
  instr_body 0x15434 (writeSuccessBlobHashesBodySpec P).
Proof.
  iStartProof. iIntros "#Hlookup #Hcode Hnext".
  iApply (write_success_blob_hashes_chunk1a P with "Hlookup Hcode").
  iApply (write_success_blob_hashes_chunk1b P with "Hlookup Hcode").
  iApply (write_success_blob_hashes_chunk1c P with "Hlookup Hcode").
  iApply (write_success_blob_hashes_chunk1d P with "Hlookup Hcode").
  iApply (write_success_blob_hashes_chunk1e P with "Hlookup Hcode").
  iExact "Hnext".
Qed.

Lemma write_success_blob_hashes_chunk2 `{!islaG Sigma} `{!threadG}
    (P : iProp Sigma) :
  instr_lookup_resources IslaTraces.write_success_blocks.Index.lookup -∗
  IslaTraces.write_success_blocks.Index.spec_instr_resources -∗
  instr_body 0x154f4 (writeSuccessBlobHashesBodySpec P) -∗
  instr_body 0x15494 (writeSuccessBlobHashesBodySpec P).
Proof.
  move => *.
  iStartProof.
  iIntros "_ #Hlookup #Hcode Hnext".
  iEval (unfold IslaTraces.write_success_blocks.Index.spec_instr_resources)
    in "Hcode".
  run_write_success_blob_chunk 0x154f4.
  liARun.
  iExists
    (tail, bytes, processed, (processed + S remaining)%nat, base, tt)ₗ.
  liARun.
  Unshelve.
  all: prepare_sidecond.
  all: try (apply bv_eq; rewrite bv_and_unsigned; assumption).
  all: try (bv_simplify_arith H1; bv_solve).
  Unshelve. all: try liARun.
Qed.

Lemma write_success_blob_hashes_chunk3 `{!islaG Sigma} `{!threadG}
    (P : iProp Sigma) :
  instr_lookup_resources IslaTraces.write_success_blocks.Index.lookup -∗
  IslaTraces.write_success_blocks.Index.spec_instr_resources -∗
  □ instr_pre 0x10190 zesuWriteOutputCallSpec -∗
  instr_body 0x15558 (writeSuccessBlobHashesTailSpec P) -∗
  instr_body 0x154f4 (writeSuccessBlobHashesBodySpec P).
Proof.
  move => *.
  iStartProof.
  iIntros "_ #Hlookup #Hcode #Houtput Hnext".
  iEval (unfold IslaTraces.write_success_blocks.Index.spec_instr_resources)
    in "Hcode".
  run_write_success_blob_chunk 0x15558.
  iExists
    (tail, bytes, remaining, processed,
     (processed + S remaining)%nat, base, tt)ₗ.
  liARun.
  Unshelve.
  all: prepare_sidecond.
  all: try (apply bv_eq; rewrite bv_and_unsigned; assumption).
  all: try (bv_simplify_arith H1; bv_solve).
  all: try bv_solve.
  all: try lia.
  all: try iFrame.
  Unshelve. all: try liARun.
Qed.

Lemma write_success_blob_hashes_tail `{!islaG Sigma} `{!threadG}
    (P : iProp Sigma) :
  instr_lookup_resources IslaTraces.write_success_blocks.Index.lookup -∗
  IslaTraces.write_success_blocks.Index.spec_instr_resources -∗
  □ instr_pre 0x10190 zesuWriteOutputCallSpec -∗
  □ instr_pre 0x153d4 (writeSuccessBlobHashesLoopSpec P) -∗
  instr_body 0x15558 (writeSuccessBlobHashesTailSpec P).
Proof.
  move => *.
  iStartProof.
  iIntros "_ #Hlookup #Hcode #Houtput #Hloop".
  iEval (unfold IslaTraces.write_success_blocks.Index.spec_instr_resources)
    in "Hcode".
  liARun.
  destruct remaining as [|remaining'].
  - exfalso. apply H11. bv_solve.
  - iExists
      (tail, bytes, remaining', S processed,
       (processed + S (S remaining'))%nat, base, tt)ₗ.
    liARun.
  Unshelve.
  all: prepare_sidecond.
  all: try (apply bv_eq; rewrite bv_and_unsigned; assumption).
  all: try (bv_simplify_arith H1; bv_solve).
  all: try lia.
  all: try iFrame.
  all: try bv_solve.
  all: have Hremaining : remaining = O by
    (bv_simplify_arith H11; bv_solve).
  all: subst remaining.
  all: cbn.
  all: try reflexivity.
  all: try (bv_simplify_arith H1; bv_solve).
Qed.

Lemma write_success_blob_hashes_loop `{!islaG Sigma} `{!threadG}
    (P : iProp Sigma) :
  instr_lookup_resources IslaTraces.write_success_blocks.Index.lookup -∗
  IslaTraces.write_success_blocks.Index.spec_instr_resources -∗
  □ instr_pre 0x10190 zesuWriteOutputCallSpec -∗
  □ instr_pre 0x153d4 (writeSuccessBlobHashesLoopSpec P) -∗
  instr_body 0x153d4 (writeSuccessBlobHashesLoopSpec P).
Proof.
  iStartProof. iIntros "#Hlookup #Hcode #Houtput #Hloop".
  iApply (write_success_blob_hashes_chunk0 P with "Hlookup Hcode").
  iApply (write_success_blob_hashes_chunk1 P with "Hlookup Hcode").
  iApply (write_success_blob_hashes_chunk2 P with "Hlookup Hcode").
  iApply (write_success_blob_hashes_chunk3 P with
    "Hlookup Hcode Houtput").
  iApply (write_success_blob_hashes_tail P with
    "Hlookup Hcode Houtput Hloop").
Qed.

Lemma write_success_blob_hashes_loop_pre `{!islaG Sigma} `{!threadG}
    (P : iProp Sigma) :
  instr_lookup_resources IslaTraces.write_success_blocks.Index.lookup -∗
  IslaTraces.write_success_blocks.Index.spec_instr_resources -∗
  □ instr_pre 0x10190 zesuWriteOutputCallSpec -∗
  □ instr_pre 0x153d4 (writeSuccessBlobHashesLoopSpec P).
Proof.
  iStartProof. iIntros "#Hlookup #Hcode #Houtput".
  iLöb as "IH".
  iModIntro. iApply instr_pre_to_body. iNext.
  iApply (write_success_blob_hashes_loop P with
    "Hlookup Hcode Houtput IH").
Qed.
