(* Generated from the pinned return trace shape. *)
From Coq Require Import Lists.List ZArith.ZArith.
Require Import isla.riscv64.riscv64.
Require Import IslaTraces.write_success_07.a15d34.
Require Import ZesuSsz.Contracts.InstructionBoundary.
Require Import ZesuSsz.Experiments.WriteSuccessSegmentAutomation.
Require Import ZesuSsz.Experiments.WriteSuccessSegment15694.

Import ListNotations.
Open Scope Z_scope.

Definition writeSuccess15d34Alignment : a_exp :=
  AExp_Binop Eq
    (AExp_Unop (Extract 1 0)
      (AExp_Val (AVal_Var "x1" []) Mk_annot) Mk_annot)
    (AExp_Val (AVal_Bits (BV 2 0)) Mk_annot) Mk_annot.

Definition writeSuccess15d34Target (ra : bv 64) : bv 64 :=
  bv_or (bv_and (ra + BV 64 0)%bv (BV 64 0xfffffffffffffffe)) (BV 64 0).
Definition writeSuccess15d34TargetBit (ra : bv 64) : bv 1 :=
  bv_extract 0 1
    (bv_shiftr (writeSuccess15d34Target ra) (BV 64 1)).

Definition writeSuccess15d34Trace1 :=
  subst_trace (Val_Bits (BV 64 0)) 2 (writeSuccessTraceTail a15d34).
Definition writeSuccess15d34Trace2 := writeSuccessTraceTail writeSuccess15d34Trace1.
Definition writeSuccess15d34Trace3 (ra : bv 64) :=
  subst_trace (Val_Bits ra) 3 (writeSuccessTraceTail writeSuccess15d34Trace2).
Definition writeSuccess15d34Trace4 ra :=
  writeSuccessTraceTail (writeSuccess15d34Trace3 ra).
Definition writeSuccess15d34Trace5 ra :=
  subst_trace (Val_Bits (Z_to_bv 64 0x15d34)) 4
    (writeSuccessTraceTail (writeSuccess15d34Trace4 ra)).
Definition writeSuccess15d34Trace6 ra :=
  writeSuccessTraceTail (writeSuccess15d34Trace5 ra).
Definition writeSuccess15d34Trace7 ra :=
  subst_trace (Val_Bits (Z_to_bv 64 0x15d34 + BV 64 4)%bv) 5
    (writeSuccessTraceTail (writeSuccess15d34Trace6 ra)).
Definition writeSuccess15d34Trace8 ra :=
  writeSuccessTraceTail (writeSuccess15d34Trace7 ra).
Definition writeSuccess15d34Trace9 ra :=
  subst_trace (Val_Bits (writeSuccess15d34Target ra)) 7
    (writeSuccessTraceTail (writeSuccess15d34Trace8 ra)).
Definition writeSuccess15d34Trace10 ra :=
  subst_trace (Val_Bits (writeSuccess15d34TargetBit ra)) 8
    (writeSuccessTraceTail (writeSuccess15d34Trace9 ra)).
Definition writeSuccess15d34Trace11 ra :=
  writeSuccessTraceTail (writeSuccess15d34Trace10 ra).

Definition writeSuccess15d34Regs regs ra : reg_map :=
  <["PC" := RVal_Bits (writeSuccess15d34Target ra)]> regs.
Definition writeSuccess15d34Before regs global : IslaState :=
  (writeSuccess15694Local a15d34 regs, global).
Definition writeSuccess15d34Done regs global ra : IslaState :=
  (writeSuccess15694Local tnil (writeSuccess15d34Regs regs ra), global).
Definition writeSuccess15d34After regs global ra : IslaState :=
  match global.(seq_instrs) !! writeSuccess15d34Target ra with
  | Some trace =>
      (writeSuccess15694Local trace (writeSuccess15d34Regs regs ra), global)
  | None =>
      ((writeSuccess15694Local tnil (writeSuccess15d34Regs regs ra))
        <| seq_nb_state := true |>, global)
  end.
Definition writeSuccess15d34DoneLabels global ra : list seq_label :=
  match global.(seq_instrs) !! writeSuccess15d34Target ra with
  | Some _ => []
  | None => [SInstrTrap (writeSuccess15d34Target ra)]
  end.

Definition writeSuccess15d34Locals regs ra : list seq_local_state :=
  [writeSuccess15694Local writeSuccess15d34Trace1 regs;
   writeSuccess15694Local writeSuccess15d34Trace2 regs;
   writeSuccess15694Local (writeSuccess15d34Trace3 ra) regs;
   writeSuccess15694Local (writeSuccess15d34Trace4 ra) regs;
   writeSuccess15694Local (writeSuccess15d34Trace5 ra) regs;
   writeSuccess15694Local (writeSuccess15d34Trace6 ra) regs;
   writeSuccess15694Local (writeSuccess15d34Trace7 ra) regs;
   writeSuccess15694Local (writeSuccess15d34Trace8 ra) regs;
   writeSuccess15694Local (writeSuccess15d34Trace9 ra) regs;
   writeSuccess15694Local (writeSuccess15d34Trace10 ra) regs;
   writeSuccess15694Local (writeSuccess15d34Trace11 ra)
     (writeSuccess15d34Regs regs ra)].
Definition writeSuccess15d34PrefixObservations regs global ra :=
  map (fun local => writeSuccess15694Observation local global)
    (writeSuccess15d34Locals regs ra).
Definition writeSuccess15d34Observations regs global ra :=
  writeSuccess15d34PrefixObservations regs global ra ++
  [({| microLabels := writeSuccess15d34DoneLabels global ra;
       microAfter := writeSuccess15d34After regs global ra |})].

Definition writeSuccess15d34Prefix8Observations regs global ra :=
  firstn 8 (writeSuccess15d34PrefixObservations regs global ra).
Definition writeSuccess15d34TailObservations regs global ra :=
  [writeSuccess15694Observation
     (writeSuccess15694Local (writeSuccess15d34Trace9 ra) regs) global;
   writeSuccess15694Observation
     (writeSuccess15694Local (writeSuccess15d34Trace10 ra) regs) global;
   writeSuccess15694Observation
     (writeSuccess15694Local (writeSuccess15d34Trace11 ra)
       (writeSuccess15d34Regs regs ra)) global;
   ({| microLabels := writeSuccess15d34DoneLabels global ra;
       microAfter := writeSuccess15d34After regs global ra |})].

Lemma writeSuccess15d34ObservationsSplit regs global ra :
  writeSuccess15d34Observations regs global ra =
    writeSuccess15d34Prefix8Observations regs global ra ++
    writeSuccess15d34TailObservations regs global ra.
Proof. reflexivity. Qed.

Lemma segment_15d34 regs global (ra : bv 64) :
  regs !! "PC" = Some (RVal_Bits (Z_to_bv 64 0x15d34)) ->
  regs !! "x1" = Some (RVal_Bits ra) ->
  global.(seq_instrs) !! Z_to_bv 64 0x15d34 = Some a15d34 ->
  eval_a_exp regs writeSuccess15694Mstatus = Some (Val_Bool true) ->
  eval_a_exp regs writeSuccess15d34Alignment = Some (Val_Bool true) ->
  IslaInstructionSegment (writeSuccess15d34Before regs global)
    (writeSuccess15d34Observations regs global ra)
    (writeSuccess15d34After regs global ra) /\
  (writeSuccess15d34After regs global ra).2.(seq_mem) = global.(seq_mem).
Proof.
  intros Hpc Hx1 Hcode Hmstatus Halign.
  assert (Hprefix : IslaInstructionPrefixPath
    (writeSuccess15d34Before regs global)
    (writeSuccess15d34PrefixObservations regs global ra)
    (writeSuccess15d34Done regs global ra)).
  {
    unfold writeSuccess15d34PrefixObservations,
    writeSuccess15d34Locals; cbn.
    eapply IslaInstructionPrefixStep; first discriminate.
    {
    apply writeSuccessSeqSilent; first reflexivity;
    unfold writeSuccess15d34Before, writeSuccess15d34Trace1,
      writeSuccessTraceTail, a15d34; cbn;
    apply DeclareConstBitVecS' with (b := BV 64 0).
    }
    eapply IslaInstructionPrefixStep; first discriminate.
    {
    apply writeSuccessSeqAssume; first reflexivity;
    unfold writeSuccess15d34Trace1, writeSuccessTraceTail, a15d34;
    cbn; apply AssumeS; exact Hmstatus.
    }
    eapply IslaInstructionPrefixStep; first discriminate.
    {
    apply writeSuccessSeqSilent; first reflexivity;
    unfold writeSuccess15d34Trace2, writeSuccess15d34Trace1,
      writeSuccessTraceTail, a15d34; cbn;
    apply DeclareConstBitVecS' with (b := ra).
    }
    eapply IslaInstructionPrefixStep; first discriminate.
    {
    apply writeSuccessSeqAssume; first reflexivity;
    unfold writeSuccess15d34Trace3, writeSuccess15d34Trace2,
      writeSuccess15d34Trace1, writeSuccessTraceTail, a15d34;
    cbn; apply AssumeS; exact Halign.
    }
    eapply IslaInstructionPrefixStep; first discriminate.
    {
    apply writeSuccessSeqSilent; first reflexivity;
    unfold writeSuccess15d34Trace4, writeSuccess15d34Trace3,
      writeSuccess15d34Trace2, writeSuccess15d34Trace1,
      writeSuccessTraceTail, a15d34; cbn;
    apply DeclareConstBitVecS' with (b := Z_to_bv 64 0x15d34).
    }
    eapply IslaInstructionPrefixStep; first discriminate.
    {
    eapply writeSuccessSeqReadReg with
      (root := RVal_Bits (Z_to_bv 64 0x15d34))
      (value := RVal_Bits (Z_to_bv 64 0x15d34));
    [reflexivity|unfold writeSuccess15d34Trace5,
      writeSuccess15d34Trace4, writeSuccess15d34Trace3,
      writeSuccess15d34Trace2, writeSuccess15d34Trace1,
      writeSuccessTraceTail, a15d34; cbn; constructor
    |exact Hpc|reflexivity|reflexivity].
    }
    eapply IslaInstructionPrefixStep; first discriminate.
    {
    apply writeSuccessSeqSilent; first reflexivity;
    unfold writeSuccess15d34Trace6, writeSuccess15d34Trace5,
      writeSuccess15d34Trace4, writeSuccess15d34Trace3,
      writeSuccess15d34Trace2, writeSuccess15d34Trace1,
      writeSuccessTraceTail, a15d34; cbn;
    eapply DefineConstS with
      (v := Val_Bits (Z_to_bv 64 0x15d34 + BV 64 4)%bv); reflexivity.
    }
    eapply IslaInstructionPrefixStep; first discriminate.
    {
    eapply writeSuccessSeqReadReg with
      (root := RVal_Bits ra) (value := RVal_Bits ra);
    [reflexivity|unfold writeSuccess15d34Trace7,
      writeSuccess15d34Trace6, writeSuccess15d34Trace5,
      writeSuccess15d34Trace4, writeSuccess15d34Trace3,
      writeSuccess15d34Trace2, writeSuccess15d34Trace1,
      writeSuccessTraceTail, a15d34; cbn; constructor
    |exact Hx1|reflexivity|reflexivity].
    }
    eapply IslaInstructionPrefixStep; first discriminate.
    {
    apply writeSuccessSeqSilent; first reflexivity;
    unfold writeSuccess15d34Trace8, writeSuccess15d34Trace7,
      writeSuccess15d34Trace6, writeSuccess15d34Trace5,
      writeSuccess15d34Trace4, writeSuccess15d34Trace3,
      writeSuccess15d34Trace2, writeSuccess15d34Trace1,
      writeSuccess15d34Target, writeSuccessTraceTail, a15d34; cbn;
    eapply DefineConstS with
      (v := Val_Bits (writeSuccess15d34Target ra)); reflexivity.
    }
    eapply IslaInstructionPrefixStep; first discriminate.
    {
    apply writeSuccessSeqSilent; first reflexivity;
    unfold writeSuccess15d34Trace9, writeSuccess15d34Trace8,
      writeSuccess15d34Trace7, writeSuccess15d34Trace6,
      writeSuccess15d34Trace5, writeSuccess15d34Trace4,
      writeSuccess15d34Trace3, writeSuccess15d34Trace2,
      writeSuccess15d34Trace1, writeSuccess15d34TargetBit,
      writeSuccess15d34Target, writeSuccessTraceTail, a15d34; cbn;
    eapply DefineConstS with
      (v := Val_Bits (writeSuccess15d34TargetBit ra)); reflexivity.
    }
    eapply IslaInstructionPrefixStep; first discriminate.
    {
    eapply writeSuccessSeqWriteReg with
      (root := RVal_Bits (Z_to_bv 64 0x15d34))
      (value := RVal_Bits (writeSuccess15d34Target ra))
      (updated := RVal_Bits (writeSuccess15d34Target ra));
    [reflexivity|unfold writeSuccess15d34Trace10,
      writeSuccess15d34Trace9, writeSuccess15d34Trace8,
      writeSuccess15d34Trace7, writeSuccess15d34Trace6,
      writeSuccess15d34Trace5, writeSuccess15d34Trace4,
      writeSuccess15d34Trace3, writeSuccess15d34Trace2,
      writeSuccess15d34Trace1, writeSuccessTraceTail, a15d34;
      cbn; constructor|exact Hpc|reflexivity|reflexivity].
    }
    apply IslaInstructionPrefixRefl.
  }
  destruct (global.(seq_instrs) !! writeSuccess15d34Target ra)
    as [targetTrace|] eqn:Htarget.
  - split.
    + unfold writeSuccess15d34Observations,
        writeSuccess15d34DoneLabels, writeSuccess15d34After.
      rewrite Htarget.
      eapply islaInstructionSegmentIntro with
        (done := writeSuccess15d34Done regs global ra)
        (labels := []) (spawned := []).
      * split; first reflexivity.
        exists (Z_to_bv 64 0x15d34), a15d34.
        cbn. rewrite Hpc Hcode. repeat split; reflexivity.
      * exact Hprefix.
      * reflexivity.
      * unfold writeSuccess15d34Done, writeSuccess15d34Regs.
        apply writeSuccessSeqDoneTabled with
          (next := targetTrace) (trace := targetTrace); try reflexivity; try constructor.
        exists (writeSuccess15d34Target ra). rewrite lookup_insert Htarget.
        repeat split; reflexivity.
      * left.
        split; first reflexivity.
        exists (writeSuccess15d34Target ra), targetTrace.
        unfold writeSuccess15d34Regs. cbn. rewrite lookup_insert Htarget.
        repeat split; reflexivity.
    + unfold writeSuccess15d34After. rewrite Htarget. reflexivity.
  - split.
    + unfold writeSuccess15d34Observations,
        writeSuccess15d34DoneLabels, writeSuccess15d34After.
      rewrite Htarget.
      eapply islaInstructionSegmentIntro with
        (done := writeSuccess15d34Done regs global ra)
        (labels := [SInstrTrap (writeSuccess15d34Target ra)])
        (spawned := []).
      * split; first reflexivity.
        exists (Z_to_bv 64 0x15d34), a15d34.
        cbn. rewrite Hpc Hcode. repeat split; reflexivity.
      * exact Hprefix.
      * reflexivity.
      * unfold writeSuccess15d34Done, writeSuccess15d34Regs.
        apply writeSuccessSeqDoneTrap with
          (next := tnil) (pc := writeSuccess15d34Target ra);
          try reflexivity; try constructor.
        -- rewrite lookup_insert. reflexivity.
        -- exact Htarget.
      * right. reflexivity.
    + unfold writeSuccess15d34After. rewrite Htarget. reflexivity.
Qed.

Lemma writeSuccess15d34RegsLookupOther regs ra reg :
  reg <> "PC" -> writeSuccess15d34Regs regs ra !! reg = regs !! reg.
Proof. intros Hne. unfold writeSuccess15d34Regs. by rewrite lookup_insert_ne. Qed.

Lemma writeSuccess15d34RegsDom regs ra :
  regs !! "PC" = Some (RVal_Bits (Z_to_bv 64 0x15d34)) ->
  dom (writeSuccess15d34Regs regs ra) = dom regs.
Proof.
  intros Hpc. apply elem_of_dom_2 in Hpc. unfold writeSuccess15d34Regs.
  rewrite dom_insert_L. set_solver.
Qed.

Print Assumptions segment_15d34.
Print Assumptions writeSuccess15d34RegsLookupOther.
Print Assumptions writeSuccess15d34RegsDom.
