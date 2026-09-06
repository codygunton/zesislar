From Coq Require Import Lists.List ZArith.ZArith.
Require Import isla.riscv64.riscv64.
From IslaTraces.write_success_blocks Require Import Index.
Require Import ZesuSsz.Contracts.InstructionBoundary.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsConcreteEntry.

Import ListNotations.

Definition writeSuccessInstructionDone (regs : reg_map) : seq_local_state := {|
  seq_trace := tnil;
  seq_regs := regs;
  seq_pc_reg := "PC";
  seq_nb_state := false
|}.

Definition writeSuccessInstructionAt
    (trace : isla_trace) (regs : reg_map) : seq_local_state := {|
  seq_trace := trace;
  seq_regs := regs;
  seq_pc_reg := "PC";
  seq_nb_state := false
|}.

Lemma writeSuccessInstructionDoneStep regs global pc trace
    (Hpc : regs !! "PC" = Some (RVal_Bits (Z_to_bv 64 pc)))
    (Hcode : global.(seq_instrs) !! Z_to_bv 64 pc = Some trace) :
  seq_step (writeSuccessInstructionDone regs) global []
    (writeSuccessInstructionAt trace regs) global [].
Proof.
  eapply (SeqStep _ _ (Some (LDone trace)) trace None).
  - reflexivity.
  - constructor.
  - simpl. split; first reflexivity.
    exists (Z_to_bv 64 pc).
    rewrite Hpc. rewrite Hcode. simpl. repeat split; reflexivity.
Qed.

Lemma writeSuccessInstructionAtBoundary regs global pc trace
    (Hpc : regs !! "PC" = Some (RVal_Bits (Z_to_bv 64 pc)))
    (Hcode : global.(seq_instrs) !! Z_to_bv 64 pc = Some trace) :
  IslaInstructionBoundary (writeSuccessInstructionAt trace regs, global).
Proof.
  split; first reflexivity. exists (Z_to_bv 64 pc), trace.
  rewrite Hpc. rewrite Hcode. repeat split; reflexivity.
Qed.

Lemma writeSuccessCompleteInstruction start prefix regs global pc trace
    (Hstart : IslaInstructionBoundary start)
    (Hprefix : IslaInstructionPrefixPath start prefix
      (writeSuccessInstructionDone regs, global))
    (Hpc : regs !! "PC" = Some (RVal_Bits (Z_to_bv 64 pc)))
    (Hcode : global.(seq_instrs) !! Z_to_bv 64 pc = Some trace) :
  exists observations,
    IslaInstructionSegment start observations
      (writeSuccessInstructionAt trace regs, global).
Proof.
  exists (prefix ++ ({| microLabels := [];
    microAfter := (writeSuccessInstructionAt trace regs, global) |} :: nil)).
  eapply islaInstructionSegmentIntro with
    (done := (writeSuccessInstructionDone regs, global))
    (labels := []) (spawned := []).
  - exact Hstart.
  - exact Hprefix.
  - reflexivity.
  - apply writeSuccessInstructionDoneStep with (pc := pc); assumption.
  - left. apply writeSuccessInstructionAtBoundary with (pc := pc); assumption.
Qed.

Ltac writeSuccessPrefixStep rule :=
  eapply IslaInstructionPrefixStep; [discriminate| |
    apply IslaInstructionPrefixRefl];
  eapply SeqStep; [reflexivity|rule|];
  simpl; repeat split; try reflexivity.

Definition writeSuccessWithdrawalsThirdResultRegs regs sp (pointer : bv 64) : reg_map :=
  <[ "PC" := RVal_Bits (Z_to_bv 64 0x156a0) ]> $
  <[ "x11" := RVal_Bits (pointer + BV 64 0)%bv ]> $
  writeSuccessWithdrawalsSecondResultRegs regs sp.

Lemma writeSuccessWithdrawalsMstatusAfterSecond regs sp :
  eval_a_exp regs writeSuccessWithdrawalsMstatusAssumption = Some (Val_Bool true) ->
  eval_a_exp (writeSuccessWithdrawalsSecondResultRegs regs sp)
    writeSuccessWithdrawalsMstatusAssumption = Some (Val_Bool true).
Proof.
  intro H. unfold writeSuccessWithdrawalsSecondResultRegs.
  rewrite !writeSuccessWithdrawalsMstatusInsert; try done.
Qed.

Lemma writeSuccessWithdrawalsThirdInstructionSegment regs global sp
    (pointer : bv 64) oldX11
    (Htable : writeSuccessWithdrawalsInstructionTable global)
    (Hx8 : regs !! "x8" = Some (RVal_Bits pointer))
    (Hx11 : regs !! "x11" = Some oldX11)
    (Hmstatus : eval_a_exp regs writeSuccessWithdrawalsMstatusAssumption =
      Some (Val_Bool true)) :
  exists observations,
    IslaInstructionSegment (writeSuccessWithdrawalsSecondAfter regs sp, global)
      observations
      (writeSuccessInstructionAt IslaTraces.write_success_90.a156a0.a156a0
        (writeSuccessWithdrawalsThirdResultRegs regs sp pointer), global).
Proof.
  assert (Hpc : (writeSuccessWithdrawalsSecondResultRegs regs sp) !! "PC" =
    Some (RVal_Bits (Z_to_bv 64 0x1569c))).
  { unfold writeSuccessWithdrawalsSecondResultRegs. apply lookup_insert. }
  assert (Hx8' : (writeSuccessWithdrawalsSecondResultRegs regs sp) !! "x8" =
    Some (RVal_Bits pointer)).
  { unfold writeSuccessWithdrawalsSecondResultRegs,
      writeSuccessWithdrawalsFirstResultRegs.
    rewrite !lookup_insert_ne; done. }
  assert (Hx11' : (writeSuccessWithdrawalsSecondResultRegs regs sp) !! "x11" =
    Some oldX11).
  { unfold writeSuccessWithdrawalsSecondResultRegs,
      writeSuccessWithdrawalsFirstResultRegs.
    rewrite !lookup_insert_ne; done. }
  assert (Hmstatus' := writeSuccessWithdrawalsMstatusAfterSecond regs sp Hmstatus).
  eapply writeSuccessCompleteInstruction with
    (regs := writeSuccessWithdrawalsThirdResultRegs regs sp pointer) (pc := 0x156a0).
  - split; first reflexivity. exists (Z_to_bv 64 0x1569c),
      IslaTraces.write_success_90.a1569c.a1569c.
    rewrite Hpc. split; first reflexivity. split; last reflexivity.
    apply Htable. left. exact Index.lookup_a1569c.
  - eapply IslaInstructionPrefixStep; first discriminate.
    { eapply SeqStep; [reflexivity|apply DeclareConstBitVecS' with (b := BV 64 0)|].
      simpl. repeat split; reflexivity. }
    eapply IslaInstructionPrefixStep; first discriminate.
    { eapply SeqStep; [reflexivity|eapply AssumeS with (b := true)|].
      - exact Hmstatus'.
      - simpl. repeat split; reflexivity. }
    eapply IslaInstructionPrefixStep; first discriminate.
    { eapply SeqStep; [reflexivity|apply DeclareConstBitVecS' with
        (b := Z_to_bv 64 0x1569c)|]. simpl. repeat split; reflexivity. }
    eapply IslaInstructionPrefixStep; first discriminate.
    { eapply SeqStep; [reflexivity|constructor|].
      simpl. exists (RVal_Bits (Z_to_bv 64 0x1569c)),
        (RVal_Bits (Z_to_bv 64 0x1569c)),
        (RVal_Bits (Z_to_bv 64 0x1569c)).
      rewrite Hpc. simpl. repeat split; try reflexivity. left. auto. }
    eapply IslaInstructionPrefixStep; first discriminate.
    { eapply SeqStep; [reflexivity|econstructor; reflexivity|].
      simpl. repeat split; reflexivity. }
    eapply IslaInstructionPrefixStep; first discriminate.
    { eapply SeqStep; [reflexivity|apply DeclareConstBitVecS' with (b := pointer)|].
      simpl. repeat split; reflexivity. }
    eapply IslaInstructionPrefixStep; first discriminate.
    { eapply SeqStep; [reflexivity|constructor|].
      simpl. exists (RVal_Bits pointer), (RVal_Bits pointer),
        (RVal_Bits pointer). rewrite Hx8'.
      simpl. repeat split; try reflexivity. left. auto. }
    eapply IslaInstructionPrefixStep; first discriminate.
    { eapply SeqStep; [reflexivity|econstructor; reflexivity|].
      simpl. repeat split; reflexivity. }
    eapply IslaInstructionPrefixStep; first discriminate.
    { eapply SeqStep; [reflexivity|constructor|].
      simpl. exists oldX11, (RVal_Bits (pointer + BV 64 0)%bv),
        (RVal_Bits (pointer + BV 64 0)%bv).
      rewrite Hx11'. repeat split; try reflexivity. }
    eapply IslaInstructionPrefixStep; first discriminate.
    { eapply SeqStep; [reflexivity|constructor|].
      simpl. exists (RVal_Bits (Z_to_bv 64 0x1569c)),
        (RVal_Bits (Z_to_bv 64 0x1569c + BV 64 4)%bv),
        (RVal_Bits (Z_to_bv 64 0x1569c + BV 64 4)%bv).
      rewrite lookup_insert_ne; last done. rewrite Hpc.
      simpl. repeat split; try reflexivity. }
    assert ((Z_to_bv 64 0x1569c + BV 64 4)%bv = Z_to_bv 64 0x156a0)
      by bv_solve. rewrite H. apply IslaInstructionPrefixRefl.
  - unfold writeSuccessWithdrawalsThirdResultRegs.
    apply lookup_insert.
  - apply Htable. left. exact Index.lookup_a156a0.
Qed.

Definition writeSuccessWithdrawalsFourthResultRegs regs sp (pointer : bv 64) : reg_map :=
  <[ "PC" := RVal_Bits (Z_to_bv 64 0x156a4) ]> $
  <[ "x1" := RVal_Bits (Z_to_bv 64 0x106a0) ]> $
  writeSuccessWithdrawalsThirdResultRegs regs sp pointer.

Lemma writeSuccessWithdrawalsMstatusAfterThird regs sp (pointer : bv 64) :
  eval_a_exp regs writeSuccessWithdrawalsMstatusAssumption = Some (Val_Bool true) ->
  eval_a_exp (writeSuccessWithdrawalsThirdResultRegs regs sp pointer)
    writeSuccessWithdrawalsMstatusAssumption = Some (Val_Bool true).
Proof.
  intro H. unfold writeSuccessWithdrawalsThirdResultRegs.
  rewrite !writeSuccessWithdrawalsMstatusInsert; try done.
Qed.

Lemma writeSuccessWithdrawalsFourthInstructionSegment regs global sp (pointer : bv 64) oldX1
    (Htable : writeSuccessWithdrawalsInstructionTable global)
    (Hx1 : regs !! "x1" = Some oldX1)
    (Hmstatus : eval_a_exp regs writeSuccessWithdrawalsMstatusAssumption =
      Some (Val_Bool true)) :
  exists observations,
    IslaInstructionSegment
      (writeSuccessInstructionAt IslaTraces.write_success_90.a156a0.a156a0
        (writeSuccessWithdrawalsThirdResultRegs regs sp pointer), global)
      observations
      (writeSuccessInstructionAt IslaTraces.write_success_90.a156a4.a156a4
        (writeSuccessWithdrawalsFourthResultRegs regs sp pointer), global).
Proof.
  assert (Hpc : (writeSuccessWithdrawalsThirdResultRegs regs sp pointer) !! "PC" =
    Some (RVal_Bits (Z_to_bv 64 0x156a0))).
  { unfold writeSuccessWithdrawalsThirdResultRegs. apply lookup_insert. }
  assert (Hx1' : (writeSuccessWithdrawalsThirdResultRegs regs sp pointer) !! "x1" = Some oldX1).
  { unfold writeSuccessWithdrawalsThirdResultRegs,
      writeSuccessWithdrawalsSecondResultRegs,
      writeSuccessWithdrawalsFirstResultRegs.
    rewrite !lookup_insert_ne; done. }
  assert (Hmstatus' := writeSuccessWithdrawalsMstatusAfterThird regs sp pointer Hmstatus).
  assert (Hlink :
    (Z_to_bv 64 0x156a0 + BV 64 0xffffffffffffb000)%bv =
      Z_to_bv 64 0x106a0) by bv_solve.
  eapply writeSuccessCompleteInstruction with
    (regs := writeSuccessWithdrawalsFourthResultRegs regs sp pointer) (pc := 0x156a4).
  - apply writeSuccessInstructionAtBoundary with (pc := 0x156a0).
    + exact Hpc.
    + apply Htable. left. exact Index.lookup_a156a0.
  - eapply IslaInstructionPrefixStep; first discriminate.
    { eapply SeqStep; [reflexivity|apply DeclareConstBitVecS' with (b := BV 64 0)|].
      simpl. repeat split; reflexivity. }
    eapply IslaInstructionPrefixStep; first discriminate.
    { eapply SeqStep; [reflexivity|eapply AssumeS with (b := true)|].
      - exact Hmstatus'.
      - simpl. repeat split; reflexivity. }
    eapply IslaInstructionPrefixStep; first discriminate.
    { eapply SeqStep; [reflexivity|apply DeclareConstBitVecS' with
        (b := Z_to_bv 64 0x156a0)|]. simpl. repeat split; reflexivity. }
    eapply IslaInstructionPrefixStep; first discriminate.
    { eapply SeqStep; [reflexivity|constructor|].
      simpl. exists (RVal_Bits (Z_to_bv 64 0x156a0)),
        (RVal_Bits (Z_to_bv 64 0x156a0)),
        (RVal_Bits (Z_to_bv 64 0x156a0)). rewrite Hpc.
      simpl. repeat split; try reflexivity. left. auto. }
    eapply IslaInstructionPrefixStep; first discriminate.
    { eapply SeqStep; [reflexivity|econstructor; reflexivity|].
      simpl. repeat split; reflexivity. }
    eapply IslaInstructionPrefixStep; first discriminate.
    { eapply SeqStep; [reflexivity|econstructor; reflexivity|].
      simpl. repeat split; reflexivity. }
    eapply IslaInstructionPrefixStep; first discriminate.
    { eapply SeqStep; [reflexivity|constructor|].
      simpl. exists oldX1, (RVal_Bits (Z_to_bv 64 0x106a0)),
        (RVal_Bits (Z_to_bv 64 0x106a0)). rewrite Hx1'.
      rewrite Hlink. repeat split; try reflexivity. }
    eapply IslaInstructionPrefixStep; first discriminate.
    { eapply SeqStep; [reflexivity|constructor|].
      simpl. exists (RVal_Bits (Z_to_bv 64 0x156a0)),
        (RVal_Bits (Z_to_bv 64 0x156a0 + BV 64 4)%bv),
        (RVal_Bits (Z_to_bv 64 0x156a0 + BV 64 4)%bv).
      rewrite lookup_insert_ne; last done. rewrite Hpc.
      simpl. repeat split; try reflexivity. }
    assert ((Z_to_bv 64 0x156a0 + BV 64 4)%bv = Z_to_bv 64 0x156a4)
      by bv_solve.
    rewrite H. apply IslaInstructionPrefixRefl.
  - unfold writeSuccessWithdrawalsFourthResultRegs. apply lookup_insert.
  - apply Htable. left. exact Index.lookup_a156a4.
Qed.

Definition writeSuccessWithdrawalsCallResultRegs regs sp (pointer : bv 64) : reg_map :=
  <[ "PC" := RVal_Bits (Z_to_bv 64 0x101d4) ]> $
  <[ "x1" := RVal_Bits (Z_to_bv 64 0x156a8) ]> $
  writeSuccessWithdrawalsFourthResultRegs regs sp pointer.

Lemma writeSuccessWithdrawalsMstatusAfterFourth regs sp (pointer : bv 64) :
  eval_a_exp regs writeSuccessWithdrawalsMstatusAssumption = Some (Val_Bool true) ->
  eval_a_exp (writeSuccessWithdrawalsFourthResultRegs regs sp pointer)
    writeSuccessWithdrawalsMstatusAssumption = Some (Val_Bool true).
Proof.
  intro H. unfold writeSuccessWithdrawalsFourthResultRegs.
  rewrite !writeSuccessWithdrawalsMstatusInsert; try done.
Qed.

Lemma writeSuccessWithdrawalsCallInstructionSegment regs global sp (pointer : bv 64)
    (Htable : writeSuccessWithdrawalsInstructionTable global)
    (Hmstatus : eval_a_exp regs writeSuccessWithdrawalsMstatusAssumption =
      Some (Val_Bool true)) :
  exists observations,
    IslaInstructionSegment
      (writeSuccessInstructionAt IslaTraces.write_success_90.a156a4.a156a4
        (writeSuccessWithdrawalsFourthResultRegs regs sp pointer), global)
      observations
      (writeSuccessInstructionAt IslaTraces.write_success_02.a101d4.a101d4
        (writeSuccessWithdrawalsCallResultRegs regs sp pointer), global).
Proof.
  assert (Hpc : (writeSuccessWithdrawalsFourthResultRegs regs sp pointer) !! "PC" =
    Some (RVal_Bits (Z_to_bv 64 0x156a4))).
  { unfold writeSuccessWithdrawalsFourthResultRegs. apply lookup_insert. }
  assert (Hx1 : (writeSuccessWithdrawalsFourthResultRegs regs sp pointer) !! "x1" =
    Some (RVal_Bits (Z_to_bv 64 0x106a0))).
  { unfold writeSuccessWithdrawalsFourthResultRegs.
    rewrite lookup_insert_ne; last done. apply lookup_insert. }
  assert (Hmstatus' := writeSuccessWithdrawalsMstatusAfterFourth regs sp pointer Hmstatus).
  assert (Hreturn :
    (Z_to_bv 64 0x156a4 + BV 64 4)%bv = Z_to_bv 64 0x156a8) by bv_solve.
  assert (Htarget :
    bv_or
      (bv_and
        (Z_to_bv 64 0x106a0 + BV 64 0xfffffffffffffb34)%bv
        (BV 64 0xfffffffffffffffe))
      (BV 64 0) = Z_to_bv 64 0x101d4) by bv_solve.
  eapply writeSuccessCompleteInstruction with
    (regs := writeSuccessWithdrawalsCallResultRegs regs sp pointer) (pc := 0x101d4).
  - apply writeSuccessInstructionAtBoundary with (pc := 0x156a4).
    + exact Hpc.
    + apply Htable. left. exact Index.lookup_a156a4.
  - eapply IslaInstructionPrefixStep; first discriminate.
    { eapply SeqStep; [reflexivity|apply DeclareConstBitVecS' with (b := BV 64 0)|].
      simpl. repeat split; reflexivity. }
    eapply IslaInstructionPrefixStep; first discriminate.
    { eapply SeqStep; [reflexivity|eapply AssumeS with (b := true)|].
      - exact Hmstatus'.
      - simpl. repeat split; reflexivity. }
    eapply IslaInstructionPrefixStep; first discriminate.
    { eapply SeqStep; [reflexivity|apply DeclareConstBitVecS' with
        (b := Z_to_bv 64 0x106a0)|]. simpl. repeat split; reflexivity. }
    eapply IslaInstructionPrefixStep; first discriminate.
    { eapply SeqStep; [reflexivity|eapply AssumeS with (b := true)|].
      - simpl. rewrite Hx1. reflexivity.
      - simpl. repeat split; reflexivity. }
    eapply IslaInstructionPrefixStep; first discriminate.
    { eapply SeqStep; [reflexivity|apply DeclareConstBitVecS' with
        (b := Z_to_bv 64 0x156a4)|]. simpl. repeat split; reflexivity. }
    eapply IslaInstructionPrefixStep; first discriminate.
    { eapply SeqStep; [reflexivity|constructor|].
      simpl. exists (RVal_Bits (Z_to_bv 64 0x156a4)),
        (RVal_Bits (Z_to_bv 64 0x156a4)),
        (RVal_Bits (Z_to_bv 64 0x156a4)). rewrite Hpc.
      simpl. repeat split; try reflexivity. left. auto. }
    eapply IslaInstructionPrefixStep; first discriminate.
    { eapply SeqStep; [reflexivity|econstructor; reflexivity|].
      simpl. repeat split; reflexivity. }
    eapply IslaInstructionPrefixStep; first discriminate.
    { eapply SeqStep; [reflexivity|constructor|].
      simpl. exists (RVal_Bits (Z_to_bv 64 0x106a0)),
        (RVal_Bits (Z_to_bv 64 0x106a0)),
        (RVal_Bits (Z_to_bv 64 0x106a0)). rewrite Hx1.
      simpl. repeat split; try reflexivity. left. auto. }
    eapply IslaInstructionPrefixStep; first discriminate.
    { eapply SeqStep; [reflexivity|econstructor; reflexivity|].
      simpl. repeat split; reflexivity. }
    eapply IslaInstructionPrefixStep; first discriminate.
    { eapply SeqStep; [reflexivity|econstructor; reflexivity|].
      simpl. repeat split; reflexivity. }
    eapply IslaInstructionPrefixStep; first discriminate.
    { eapply SeqStep; [reflexivity|constructor|].
      simpl. exists (RVal_Bits (Z_to_bv 64 0x106a0)),
        (RVal_Bits (Z_to_bv 64 0x156a8)),
        (RVal_Bits (Z_to_bv 64 0x156a8)). rewrite Hx1. rewrite Hreturn.
      repeat split; try reflexivity. }
    eapply IslaInstructionPrefixStep; first discriminate.
    { eapply SeqStep; [reflexivity|constructor|].
      simpl. exists (RVal_Bits (Z_to_bv 64 0x156a4)),
        (RVal_Bits (Z_to_bv 64 0x101d4)),
        (RVal_Bits (Z_to_bv 64 0x101d4)).
      rewrite lookup_insert_ne; last done. rewrite Hpc. rewrite Htarget.
      simpl. repeat split; try reflexivity. }
    apply IslaInstructionPrefixRefl.
  - unfold writeSuccessWithdrawalsCallResultRegs. apply lookup_insert.
  - apply Htable. right. right. left. cbn. tauto.
Qed.

Definition writeSuccessWithdrawalsMemcpyFirstResultRegs regs sp
    (pointer : bv 64) : reg_map :=
  <[ "PC" := RVal_Bits (Z_to_bv 64 0x101d8) ]> $
  <[ "x15" := RVal_Bits (BV 64 0) ]> $
  writeSuccessWithdrawalsCallResultRegs regs sp pointer.

Lemma writeSuccessWithdrawalsMstatusAtCall regs sp (pointer : bv 64) :
  eval_a_exp regs writeSuccessWithdrawalsMstatusAssumption = Some (Val_Bool true) ->
  eval_a_exp (writeSuccessWithdrawalsCallResultRegs regs sp pointer)
    writeSuccessWithdrawalsMstatusAssumption = Some (Val_Bool true).
Proof.
  intro H. unfold writeSuccessWithdrawalsCallResultRegs.
  rewrite !writeSuccessWithdrawalsMstatusInsert; try done.
Qed.

Lemma writeSuccessWithdrawalsMemcpyFirstInstructionSegment regs global sp
    (pointer : bv 64) oldX15
    (Htable : writeSuccessWithdrawalsInstructionTable global)
    (Hx15 : regs !! "x15" = Some oldX15)
    (Hmstatus : eval_a_exp regs writeSuccessWithdrawalsMstatusAssumption =
      Some (Val_Bool true)) :
  exists observations,
    IslaInstructionSegment
      (writeSuccessInstructionAt IslaTraces.write_success_02.a101d4.a101d4
        (writeSuccessWithdrawalsCallResultRegs regs sp pointer), global)
      observations
      (writeSuccessInstructionAt IslaTraces.write_success_02.a101d8.a101d8
        (writeSuccessWithdrawalsMemcpyFirstResultRegs regs sp pointer), global).
Proof.
  assert (Hpc : (writeSuccessWithdrawalsCallResultRegs regs sp pointer) !! "PC" =
    Some (RVal_Bits (Z_to_bv 64 0x101d4))).
  { unfold writeSuccessWithdrawalsCallResultRegs. apply lookup_insert. }
  assert (Hx15' : (writeSuccessWithdrawalsCallResultRegs regs sp pointer) !! "x15" =
    Some oldX15).
  { unfold writeSuccessWithdrawalsCallResultRegs,
      writeSuccessWithdrawalsFourthResultRegs,
      writeSuccessWithdrawalsThirdResultRegs,
      writeSuccessWithdrawalsSecondResultRegs,
      writeSuccessWithdrawalsFirstResultRegs.
    rewrite !lookup_insert_ne; done. }
  assert (Hmstatus' := writeSuccessWithdrawalsMstatusAtCall regs sp pointer Hmstatus).
  eapply writeSuccessCompleteInstruction with
    (regs := writeSuccessWithdrawalsMemcpyFirstResultRegs regs sp pointer)
    (pc := 0x101d8).
  - apply writeSuccessInstructionAtBoundary with (pc := 0x101d4).
    + exact Hpc.
    + apply Htable. right. right. left. cbn. tauto.
  - eapply IslaInstructionPrefixStep; first discriminate.
    { eapply SeqStep; [reflexivity|apply DeclareConstBitVecS' with (b := BV 64 0)|].
      simpl. repeat split; reflexivity. }
    eapply IslaInstructionPrefixStep; first discriminate.
    { eapply SeqStep; [reflexivity|eapply AssumeS with (b := true)|].
      - exact Hmstatus'.
      - simpl. repeat split; reflexivity. }
    eapply IslaInstructionPrefixStep; first discriminate.
    { eapply SeqStep; [reflexivity|apply DeclareConstBitVecS' with
        (b := Z_to_bv 64 0x101d4)|]. simpl. repeat split; reflexivity. }
    eapply IslaInstructionPrefixStep; first discriminate.
    { eapply SeqStep; [reflexivity|constructor|].
      simpl. exists (RVal_Bits (Z_to_bv 64 0x101d4)),
        (RVal_Bits (Z_to_bv 64 0x101d4)),
        (RVal_Bits (Z_to_bv 64 0x101d4)). rewrite Hpc.
      simpl. repeat split; try reflexivity. left. auto. }
    eapply IslaInstructionPrefixStep; first discriminate.
    { eapply SeqStep; [reflexivity|econstructor; reflexivity|].
      simpl. repeat split; reflexivity. }
    eapply IslaInstructionPrefixStep; first discriminate.
    { eapply SeqStep; [reflexivity|constructor|].
      simpl. exists oldX15, (RVal_Bits (BV 64 0)), (RVal_Bits (BV 64 0)).
      rewrite Hx15'. repeat split; try reflexivity. }
    eapply IslaInstructionPrefixStep; first discriminate.
    { eapply SeqStep; [reflexivity|constructor|].
      simpl. exists (RVal_Bits (Z_to_bv 64 0x101d4)),
        (RVal_Bits (Z_to_bv 64 0x101d4 + BV 64 4)%bv),
        (RVal_Bits (Z_to_bv 64 0x101d4 + BV 64 4)%bv).
      rewrite lookup_insert_ne; last done. rewrite Hpc.
      simpl. repeat split; try reflexivity. }
    assert ((Z_to_bv 64 0x101d4 + BV 64 4)%bv = Z_to_bv 64 0x101d8)
      by bv_solve. rewrite H. apply IslaInstructionPrefixRefl.
  - unfold writeSuccessWithdrawalsMemcpyFirstResultRegs. apply lookup_insert.
  - apply Htable. right. right. left. cbn. tauto.
Qed.

Print Assumptions writeSuccessCompleteInstruction.
Print Assumptions writeSuccessWithdrawalsThirdInstructionSegment.
Print Assumptions writeSuccessWithdrawalsFourthInstructionSegment.
Print Assumptions writeSuccessWithdrawalsCallInstructionSegment.
Print Assumptions writeSuccessWithdrawalsMemcpyFirstInstructionSegment.

