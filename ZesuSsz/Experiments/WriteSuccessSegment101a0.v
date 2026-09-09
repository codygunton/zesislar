(* Generated from the pinned return trace shape. *)
From Coq Require Import Lists.List ZArith.ZArith.
Require Import isla.riscv64.riscv64.
Require Import IslaTraces.write_success_01.a101a0.
Require Import ZesuSsz.Contracts.InstructionBoundary.
Require Import ZesuSsz.Experiments.WriteSuccessSegmentAutomation.
Require Import ZesuSsz.Experiments.WriteSuccessSegment15694.

Import ListNotations.
Open Scope Z_scope.

Definition writeSuccess101a0Alignment : a_exp :=
  AExp_Binop Eq
    (AExp_Unop (Extract 1 0)
      (AExp_Val (AVal_Var "x1" []) Mk_annot) Mk_annot)
    (AExp_Val (AVal_Bits (BV 2 0)) Mk_annot) Mk_annot.

Definition writeSuccess101a0Target (ra : bv 64) : bv 64 :=
  bv_or (bv_and (ra + BV 64 0)%bv (BV 64 0xfffffffffffffffe)) (BV 64 0).
Definition writeSuccess101a0TargetBit (ra : bv 64) : bv 1 :=
  bv_extract 0 1
    (bv_shiftr (writeSuccess101a0Target ra) (BV 64 1)).

Definition writeSuccess101a0Trace1 :=
  subst_trace (Val_Bits (BV 64 0)) 2 (writeSuccessTraceTail a101a0).
Definition writeSuccess101a0Trace2 := writeSuccessTraceTail writeSuccess101a0Trace1.
Definition writeSuccess101a0Trace3 (ra : bv 64) :=
  subst_trace (Val_Bits ra) 3 (writeSuccessTraceTail writeSuccess101a0Trace2).
Definition writeSuccess101a0Trace4 ra :=
  writeSuccessTraceTail (writeSuccess101a0Trace3 ra).
Definition writeSuccess101a0Trace5 ra :=
  subst_trace (Val_Bits (Z_to_bv 64 0x101a0)) 4
    (writeSuccessTraceTail (writeSuccess101a0Trace4 ra)).
Definition writeSuccess101a0Trace6 ra :=
  writeSuccessTraceTail (writeSuccess101a0Trace5 ra).
Definition writeSuccess101a0Trace7 ra :=
  subst_trace (Val_Bits (Z_to_bv 64 0x101a0 + BV 64 4)%bv) 5
    (writeSuccessTraceTail (writeSuccess101a0Trace6 ra)).
Definition writeSuccess101a0Trace8 ra :=
  writeSuccessTraceTail (writeSuccess101a0Trace7 ra).
Definition writeSuccess101a0Trace9 ra :=
  subst_trace (Val_Bits (writeSuccess101a0Target ra)) 7
    (writeSuccessTraceTail (writeSuccess101a0Trace8 ra)).
Definition writeSuccess101a0Trace10 ra :=
  subst_trace (Val_Bits (writeSuccess101a0TargetBit ra)) 8
    (writeSuccessTraceTail (writeSuccess101a0Trace9 ra)).
Definition writeSuccess101a0Trace11 ra :=
  writeSuccessTraceTail (writeSuccess101a0Trace10 ra).

Definition writeSuccess101a0Regs regs ra : reg_map :=
  <["PC" := RVal_Bits (writeSuccess101a0Target ra)]> regs.
Definition writeSuccess101a0Before regs global : IslaState :=
  (writeSuccess15694Local a101a0 regs, global).
Definition writeSuccess101a0Done regs global ra : IslaState :=
  (writeSuccess15694Local tnil (writeSuccess101a0Regs regs ra), global).
Definition writeSuccess101a0After regs global ra : IslaState :=
  match global.(seq_instrs) !! writeSuccess101a0Target ra with
  | Some trace =>
      (writeSuccess15694Local trace (writeSuccess101a0Regs regs ra), global)
  | None =>
      ((writeSuccess15694Local tnil (writeSuccess101a0Regs regs ra))
        <| seq_nb_state := true |>, global)
  end.
Definition writeSuccess101a0DoneLabels global ra : list seq_label :=
  match global.(seq_instrs) !! writeSuccess101a0Target ra with
  | Some _ => []
  | None => [SInstrTrap (writeSuccess101a0Target ra)]
  end.

Definition writeSuccess101a0Locals regs ra : list seq_local_state :=
  [writeSuccess15694Local writeSuccess101a0Trace1 regs;
   writeSuccess15694Local writeSuccess101a0Trace2 regs;
   writeSuccess15694Local (writeSuccess101a0Trace3 ra) regs;
   writeSuccess15694Local (writeSuccess101a0Trace4 ra) regs;
   writeSuccess15694Local (writeSuccess101a0Trace5 ra) regs;
   writeSuccess15694Local (writeSuccess101a0Trace6 ra) regs;
   writeSuccess15694Local (writeSuccess101a0Trace7 ra) regs;
   writeSuccess15694Local (writeSuccess101a0Trace8 ra) regs;
   writeSuccess15694Local (writeSuccess101a0Trace9 ra) regs;
   writeSuccess15694Local (writeSuccess101a0Trace10 ra) regs;
   writeSuccess15694Local (writeSuccess101a0Trace11 ra)
     (writeSuccess101a0Regs regs ra)].
Definition writeSuccess101a0PrefixObservations regs global ra :=
  map (fun local => writeSuccess15694Observation local global)
    (writeSuccess101a0Locals regs ra).
Definition writeSuccess101a0Observations regs global ra :=
  writeSuccess101a0PrefixObservations regs global ra ++
  [({| microLabels := writeSuccess101a0DoneLabels global ra;
       microAfter := writeSuccess101a0After regs global ra |})].

Definition writeSuccess101a0Prefix8Observations regs global ra :=
  firstn 8 (writeSuccess101a0PrefixObservations regs global ra).
Definition writeSuccess101a0TailObservations regs global ra :=
  [writeSuccess15694Observation
     (writeSuccess15694Local (writeSuccess101a0Trace9 ra) regs) global;
   writeSuccess15694Observation
     (writeSuccess15694Local (writeSuccess101a0Trace10 ra) regs) global;
   writeSuccess15694Observation
     (writeSuccess15694Local (writeSuccess101a0Trace11 ra)
       (writeSuccess101a0Regs regs ra)) global;
   ({| microLabels := writeSuccess101a0DoneLabels global ra;
       microAfter := writeSuccess101a0After regs global ra |})].

Lemma writeSuccess101a0ObservationsSplit regs global ra :
  writeSuccess101a0Observations regs global ra =
    writeSuccess101a0Prefix8Observations regs global ra ++
    writeSuccess101a0TailObservations regs global ra.
Proof. reflexivity. Qed.

Lemma segment_101a0 regs global (ra : bv 64) :
  regs !! "PC" = Some (RVal_Bits (Z_to_bv 64 0x101a0)) ->
  regs !! "x1" = Some (RVal_Bits ra) ->
  global.(seq_instrs) !! Z_to_bv 64 0x101a0 = Some a101a0 ->
  eval_a_exp regs writeSuccess15694Mstatus = Some (Val_Bool true) ->
  eval_a_exp regs writeSuccess101a0Alignment = Some (Val_Bool true) ->
  IslaInstructionSegment (writeSuccess101a0Before regs global)
    (writeSuccess101a0Observations regs global ra)
    (writeSuccess101a0After regs global ra) /\
  (writeSuccess101a0After regs global ra).2.(seq_mem) = global.(seq_mem).
Proof.
  intros Hpc Hx1 Hcode Hmstatus Halign.
  assert (Hprefix : IslaInstructionPrefixPath
    (writeSuccess101a0Before regs global)
    (writeSuccess101a0PrefixObservations regs global ra)
    (writeSuccess101a0Done regs global ra)).
  {
    unfold writeSuccess101a0PrefixObservations,
    writeSuccess101a0Locals; cbn.
    eapply IslaInstructionPrefixStep; first discriminate.
    {
    apply writeSuccessSeqSilent; first reflexivity;
    unfold writeSuccess101a0Before, writeSuccess101a0Trace1,
      writeSuccessTraceTail, a101a0; cbn;
    apply DeclareConstBitVecS' with (b := BV 64 0).
    }
    eapply IslaInstructionPrefixStep; first discriminate.
    {
    apply writeSuccessSeqAssume; first reflexivity;
    unfold writeSuccess101a0Trace1, writeSuccessTraceTail, a101a0;
    cbn; apply AssumeS; exact Hmstatus.
    }
    eapply IslaInstructionPrefixStep; first discriminate.
    {
    apply writeSuccessSeqSilent; first reflexivity;
    unfold writeSuccess101a0Trace2, writeSuccess101a0Trace1,
      writeSuccessTraceTail, a101a0; cbn;
    apply DeclareConstBitVecS' with (b := ra).
    }
    eapply IslaInstructionPrefixStep; first discriminate.
    {
    apply writeSuccessSeqAssume; first reflexivity;
    unfold writeSuccess101a0Trace3, writeSuccess101a0Trace2,
      writeSuccess101a0Trace1, writeSuccessTraceTail, a101a0;
    cbn; apply AssumeS; exact Halign.
    }
    eapply IslaInstructionPrefixStep; first discriminate.
    {
    apply writeSuccessSeqSilent; first reflexivity;
    unfold writeSuccess101a0Trace4, writeSuccess101a0Trace3,
      writeSuccess101a0Trace2, writeSuccess101a0Trace1,
      writeSuccessTraceTail, a101a0; cbn;
    apply DeclareConstBitVecS' with (b := Z_to_bv 64 0x101a0).
    }
    eapply IslaInstructionPrefixStep; first discriminate.
    {
    eapply writeSuccessSeqReadReg with
      (root := RVal_Bits (Z_to_bv 64 0x101a0))
      (value := RVal_Bits (Z_to_bv 64 0x101a0));
    [reflexivity|unfold writeSuccess101a0Trace5,
      writeSuccess101a0Trace4, writeSuccess101a0Trace3,
      writeSuccess101a0Trace2, writeSuccess101a0Trace1,
      writeSuccessTraceTail, a101a0; cbn; constructor
    |exact Hpc|reflexivity|reflexivity].
    }
    eapply IslaInstructionPrefixStep; first discriminate.
    {
    apply writeSuccessSeqSilent; first reflexivity;
    unfold writeSuccess101a0Trace6, writeSuccess101a0Trace5,
      writeSuccess101a0Trace4, writeSuccess101a0Trace3,
      writeSuccess101a0Trace2, writeSuccess101a0Trace1,
      writeSuccessTraceTail, a101a0; cbn;
    eapply DefineConstS with
      (v := Val_Bits (Z_to_bv 64 0x101a0 + BV 64 4)%bv); reflexivity.
    }
    eapply IslaInstructionPrefixStep; first discriminate.
    {
    eapply writeSuccessSeqReadReg with
      (root := RVal_Bits ra) (value := RVal_Bits ra);
    [reflexivity|unfold writeSuccess101a0Trace7,
      writeSuccess101a0Trace6, writeSuccess101a0Trace5,
      writeSuccess101a0Trace4, writeSuccess101a0Trace3,
      writeSuccess101a0Trace2, writeSuccess101a0Trace1,
      writeSuccessTraceTail, a101a0; cbn; constructor
    |exact Hx1|reflexivity|reflexivity].
    }
    eapply IslaInstructionPrefixStep; first discriminate.
    {
    apply writeSuccessSeqSilent; first reflexivity;
    unfold writeSuccess101a0Trace8, writeSuccess101a0Trace7,
      writeSuccess101a0Trace6, writeSuccess101a0Trace5,
      writeSuccess101a0Trace4, writeSuccess101a0Trace3,
      writeSuccess101a0Trace2, writeSuccess101a0Trace1,
      writeSuccess101a0Target, writeSuccessTraceTail, a101a0; cbn;
    eapply DefineConstS with
      (v := Val_Bits (writeSuccess101a0Target ra)); reflexivity.
    }
    eapply IslaInstructionPrefixStep; first discriminate.
    {
    apply writeSuccessSeqSilent; first reflexivity;
    unfold writeSuccess101a0Trace9, writeSuccess101a0Trace8,
      writeSuccess101a0Trace7, writeSuccess101a0Trace6,
      writeSuccess101a0Trace5, writeSuccess101a0Trace4,
      writeSuccess101a0Trace3, writeSuccess101a0Trace2,
      writeSuccess101a0Trace1, writeSuccess101a0TargetBit,
      writeSuccess101a0Target, writeSuccessTraceTail, a101a0; cbn;
    eapply DefineConstS with
      (v := Val_Bits (writeSuccess101a0TargetBit ra)); reflexivity.
    }
    eapply IslaInstructionPrefixStep; first discriminate.
    {
    eapply writeSuccessSeqWriteReg with
      (root := RVal_Bits (Z_to_bv 64 0x101a0))
      (value := RVal_Bits (writeSuccess101a0Target ra))
      (updated := RVal_Bits (writeSuccess101a0Target ra));
    [reflexivity|unfold writeSuccess101a0Trace10,
      writeSuccess101a0Trace9, writeSuccess101a0Trace8,
      writeSuccess101a0Trace7, writeSuccess101a0Trace6,
      writeSuccess101a0Trace5, writeSuccess101a0Trace4,
      writeSuccess101a0Trace3, writeSuccess101a0Trace2,
      writeSuccess101a0Trace1, writeSuccessTraceTail, a101a0;
      cbn; constructor|exact Hpc|reflexivity|reflexivity].
    }
    apply IslaInstructionPrefixRefl.
  }
  destruct (global.(seq_instrs) !! writeSuccess101a0Target ra)
    as [targetTrace|] eqn:Htarget.
  - split.
    + unfold writeSuccess101a0Observations,
        writeSuccess101a0DoneLabels, writeSuccess101a0After.
      rewrite Htarget.
      eapply islaInstructionSegmentIntro with
        (done := writeSuccess101a0Done regs global ra)
        (labels := []) (spawned := []).
      * split; first reflexivity.
        exists (Z_to_bv 64 0x101a0), a101a0.
        cbn. rewrite Hpc Hcode. repeat split; reflexivity.
      * exact Hprefix.
      * reflexivity.
      * unfold writeSuccess101a0Done, writeSuccess101a0Regs.
        apply writeSuccessSeqDoneTabled with
          (next := targetTrace) (trace := targetTrace); try reflexivity; try constructor.
        exists (writeSuccess101a0Target ra). rewrite lookup_insert Htarget.
        repeat split; reflexivity.
      * left.
        split; first reflexivity.
        exists (writeSuccess101a0Target ra), targetTrace.
        unfold writeSuccess101a0Regs. cbn. rewrite lookup_insert Htarget.
        repeat split; reflexivity.
    + unfold writeSuccess101a0After. rewrite Htarget. reflexivity.
  - split.
    + unfold writeSuccess101a0Observations,
        writeSuccess101a0DoneLabels, writeSuccess101a0After.
      rewrite Htarget.
      eapply islaInstructionSegmentIntro with
        (done := writeSuccess101a0Done regs global ra)
        (labels := [SInstrTrap (writeSuccess101a0Target ra)])
        (spawned := []).
      * split; first reflexivity.
        exists (Z_to_bv 64 0x101a0), a101a0.
        cbn. rewrite Hpc Hcode. repeat split; reflexivity.
      * exact Hprefix.
      * reflexivity.
      * unfold writeSuccess101a0Done, writeSuccess101a0Regs.
        apply writeSuccessSeqDoneTrap with
          (next := tnil) (pc := writeSuccess101a0Target ra);
          try reflexivity; try constructor.
        -- rewrite lookup_insert. reflexivity.
        -- exact Htarget.
      * right. reflexivity.
    + unfold writeSuccess101a0After. rewrite Htarget. reflexivity.
Qed.

Lemma writeSuccess101a0RegsLookupOther regs ra reg :
  reg <> "PC" -> writeSuccess101a0Regs regs ra !! reg = regs !! reg.
Proof. intros Hne. unfold writeSuccess101a0Regs. by rewrite lookup_insert_ne. Qed.

Lemma writeSuccess101a0RegsDom regs ra :
  regs !! "PC" = Some (RVal_Bits (Z_to_bv 64 0x101a0)) ->
  dom (writeSuccess101a0Regs regs ra) = dom regs.
Proof.
  intros Hpc. apply elem_of_dom_2 in Hpc. unfold writeSuccess101a0Regs.
  rewrite dom_insert_L. set_solver.
Qed.

Print Assumptions segment_101a0.
Print Assumptions writeSuccess101a0RegsLookupOther.
Print Assumptions writeSuccess101a0RegsDom.
