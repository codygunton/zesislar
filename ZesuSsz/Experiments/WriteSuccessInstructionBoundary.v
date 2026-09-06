From Coq Require Import Lists.List ZArith.ZArith.
Require Import isla.riscv64.riscv64.
From IslaTraces.write_success_00 Require Import instrs.
Require Import ZesuSsz.Contracts.InstructionBoundary.

Import ListNotations.

Definition writeSuccessFirstGlobal (mem : mem_map) : seq_global_state := {|
  seq_instrs :=
    <[ (BV 64 0x14d30) := a14d30 ]> $
    <[ (BV 64 0x14d34) := a14d34 ]> $
    ∅;
  seq_mem := mem
|}.

Definition writeSuccessFirstLocal (regs : reg_map) : seq_local_state := {|
  seq_trace := a14d30;
  seq_regs := regs;
  seq_pc_reg := "PC";
  seq_nb_state := false
|}.

Lemma writeSuccessFirstBoundary regs mem
    (Hpc : regs !! "PC" = Some (RVal_Bits (BV 64 0x14d30))) :
  IslaInstructionBoundary
    (writeSuccessFirstLocal regs, writeSuccessFirstGlobal mem).
Proof.
  split; first reflexivity.
  exists (BV 64 0x14d30), a14d30. split; first exact Hpc.
  split; last reflexivity.
  change (Some a14d30 = Some a14d30). reflexivity.
Qed.

Definition writeSuccessMstatusAssumption : a_exp :=
  AExp_Binop Eq
    (AExp_Manyop (Bvmanyarith Bvand)
      [AExp_Val (AVal_Var "mstatus" [Field "bits"]) Mk_annot;
       AExp_Val (AVal_Bits (BV 64 0x20000)) Mk_annot] Mk_annot)
    (AExp_Val (AVal_Bits (BV 64 0)) Mk_annot) Mk_annot.

Definition writeSuccessFirstResultRegs (regs : reg_map) : reg_map :=
  <[ "PC" := RVal_Bits (BV 64 0x14d34) ]> $
  <[ "x2" := RVal_Bits (BV 64 0x20000830) ]> regs.

Definition writeSuccessFirstDone (regs : reg_map) : seq_local_state := {|
  seq_trace := tnil;
  seq_regs := writeSuccessFirstResultRegs regs;
  seq_pc_reg := "PC";
  seq_nb_state := false
|}.

Lemma writeSuccessFirstInstructionMicroPath regs mem
    (Hpc : regs !! "PC" = Some (RVal_Bits (BV 64 0x14d30)))
    (Hsp : regs !! "x2" = Some (RVal_Bits (BV 64 0x20001000)))
    (Hmstatus : eval_a_exp regs writeSuccessMstatusAssumption =
      Some (Val_Bool true)) :
  exists observations,
    IslaInstructionPrefixPath (writeSuccessFirstLocal regs, writeSuccessFirstGlobal mem)
      observations (writeSuccessFirstDone regs, writeSuccessFirstGlobal mem).
Proof.
  eexists.
  - eapply IslaInstructionPrefixStep.
    { discriminate. }
    { eapply SeqStep.
      - reflexivity.
      - apply DeclareConstBitVecS' with (b := BV 64 0).
      - simpl. repeat split; reflexivity. }
    eapply IslaInstructionPrefixStep.
    { discriminate. }
    { eapply SeqStep.
      - reflexivity.
      - eapply AssumeS with (b := true). exact Hmstatus.
      - simpl. repeat split; reflexivity. }
    eapply IslaInstructionPrefixStep.
    { discriminate. }
    { eapply SeqStep.
      - reflexivity.
      - apply DeclareConstBitVecS' with (b := BV 64 0x14d30).
      - simpl. repeat split; reflexivity. }
    eapply IslaInstructionPrefixStep.
    { discriminate. }
    { eapply SeqStep.
      - reflexivity.
      - constructor.
      - simpl. exists (RVal_Bits (BV 64 0x14d30)).
        exists (RVal_Bits (BV 64 0x14d30)).
        exists (RVal_Bits (BV 64 0x14d30)).
        rewrite Hpc. simpl. repeat split; try reflexivity. left. auto. }
    eapply IslaInstructionPrefixStep.
    { discriminate. }
    { eapply SeqStep.
      - reflexivity.
      - econstructor. reflexivity.
      - simpl. repeat split; reflexivity. }
    eapply IslaInstructionPrefixStep.
    { discriminate. }
    { eapply SeqStep.
      - reflexivity.
      - apply DeclareConstBitVecS' with (b := BV 64 0x20001000).
      - simpl. repeat split; reflexivity. }
    eapply IslaInstructionPrefixStep.
    { discriminate. }
    { eapply SeqStep.
      - reflexivity.
      - constructor.
      - simpl. exists (RVal_Bits (BV 64 0x20001000)).
        exists (RVal_Bits (BV 64 0x20001000)).
        exists (RVal_Bits (BV 64 0x20001000)).
        rewrite Hsp. simpl. repeat split; try reflexivity. left. auto. }
    eapply IslaInstructionPrefixStep.
    { discriminate. }
    { eapply SeqStep.
      - reflexivity.
      - econstructor. reflexivity.
      - simpl. repeat split; reflexivity. }
    eapply IslaInstructionPrefixStep.
    { discriminate. }
    { eapply SeqStep.
      - reflexivity.
      - constructor.
      - simpl. repeat eexists. rewrite Hsp. simpl.
        repeat split; eauto. }
    eapply IslaInstructionPrefixStep.
    { discriminate. }
    { eapply SeqStep.
      - reflexivity.
      - constructor.
      - simpl. repeat eexists. simplify_map_eq.
        repeat split; eauto. }
    assert (Hpcadd : (BV 64 0x14d30 + BV 64 4)%bv = BV 64 0x14d34)
      by bv_solve.
    assert (Hspadd :
      (BV 64 0x20001000 + BV 64 0xfffffffffffff830)%bv =
        BV 64 0x20000830) by bv_solve.
    rewrite Hpcadd Hspadd.
    apply IslaInstructionPrefixRefl.
Qed.

Print Assumptions writeSuccessFirstBoundary.
Print Assumptions writeSuccessFirstInstructionMicroPath.

Definition writeSuccessFirstAfter (regs : reg_map) : seq_local_state := {|
  seq_trace := a14d34;
  seq_regs := writeSuccessFirstResultRegs regs;
  seq_pc_reg := "PC";
  seq_nb_state := false
|}.

Lemma writeSuccessFirstDoneStep regs mem :
  seq_step (writeSuccessFirstDone regs) (writeSuccessFirstGlobal mem) []
    (writeSuccessFirstAfter regs) (writeSuccessFirstGlobal mem) [].
Proof.
  eapply (SeqStep _ _ (Some (LDone a14d34)) a14d34 None).
  - reflexivity.
  - constructor.
  - simpl. split; first reflexivity.
    exists (BV 64 0x14d34). split.
    + unfold writeSuccessFirstResultRegs.
      apply lookup_insert.
    + assert (Hinstr :
          (writeSuccessFirstGlobal mem).(seq_instrs) !! (BV 64 0x14d34) =
            Some a14d34).
      { simpl. rewrite lookup_insert_ne; last bv_solve. apply lookup_insert. }
      rewrite Hinstr. simpl. repeat split; reflexivity.
Qed.

Lemma writeSuccessFirstAfterBoundary regs mem :
  IslaInstructionBoundary
    (writeSuccessFirstAfter regs, writeSuccessFirstGlobal mem).
Proof.
  split; first reflexivity.
  exists (BV 64 0x14d34), a14d34.
  split.
  - unfold writeSuccessFirstResultRegs. apply lookup_insert.
  - split; last reflexivity.
    simpl. rewrite lookup_insert_ne; last bv_solve. apply lookup_insert.
Qed.

Lemma writeSuccessFirstInstructionExample regs mem
    (Hpc : regs !! "PC" = Some (RVal_Bits (BV 64 0x14d30)))
    (Hsp : regs !! "x2" = Some (RVal_Bits (BV 64 0x20001000)))
    (Hmstatus : eval_a_exp regs writeSuccessMstatusAssumption =
      Some (Val_Bool true)) :
  exists observations,
    IslaInstructionSegment
      (writeSuccessFirstLocal regs, writeSuccessFirstGlobal mem)
      observations
      (writeSuccessFirstAfter regs, writeSuccessFirstGlobal mem).
Proof.
  destruct (writeSuccessFirstInstructionMicroPath regs mem Hpc Hsp Hmstatus)
    as [prefix Hprefix].
  exists (prefix ++
    (({| microLabels := [];
         microAfter :=
           (writeSuccessFirstAfter regs, writeSuccessFirstGlobal mem) |}) :: [])).
  eapply Build_IslaInstructionSegment
    with (instructionSegmentDoneSource :=
            (writeSuccessFirstDone regs, writeSuccessFirstGlobal mem))
         (instructionSegmentPrefix := prefix)
         (instructionSegmentLabels := [])
         (instructionSegmentSpawned := []).
  - apply writeSuccessFirstBoundary. exact Hpc.
  - exact Hprefix.
  - reflexivity.
  - apply writeSuccessFirstDoneStep.
  - reflexivity.
  - left. apply writeSuccessFirstAfterBoundary.
Qed.

Print Assumptions writeSuccessFirstDoneStep.
Print Assumptions writeSuccessFirstInstructionExample.
