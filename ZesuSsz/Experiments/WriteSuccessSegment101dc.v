(* Generated from the pinned return trace shape. *)
From Coq Require Import Lists.List ZArith.ZArith.
Require Import isla.riscv64.riscv64.
Require Import IslaTraces.write_success_02.a101dc.
Require Import ZesuSsz.Contracts.InstructionBoundary.
Require Import ZesuSsz.Experiments.WriteSuccessSegmentAutomation.
Require Import ZesuSsz.Experiments.WriteSuccessSegment15694.

Import ListNotations.
Open Scope Z_scope.

Definition writeSuccess101dcAlignment : a_exp :=
  AExp_Binop Eq
    (AExp_Unop (Extract 1 0)
      (AExp_Val (AVal_Var "x1" []) Mk_annot) Mk_annot)
    (AExp_Val (AVal_Bits (BV 2 0)) Mk_annot) Mk_annot.

Definition writeSuccess101dcTarget (ra : bv 64) : bv 64 :=
  bv_or (bv_and (ra + BV 64 0)%bv (BV 64 0xfffffffffffffffe)) (BV 64 0).
Definition writeSuccess101dcTargetBit (ra : bv 64) : bv 1 :=
  bv_extract 0 1
    (bv_shiftr (writeSuccess101dcTarget ra) (BV 64 1)).

Definition writeSuccess101dcTrace1 :=
  subst_trace (Val_Bits (BV 64 0)) 2 (writeSuccessTraceTail a101dc).
Definition writeSuccess101dcTrace2 := writeSuccessTraceTail writeSuccess101dcTrace1.
Definition writeSuccess101dcTrace3 (ra : bv 64) :=
  subst_trace (Val_Bits ra) 3 (writeSuccessTraceTail writeSuccess101dcTrace2).
Definition writeSuccess101dcTrace4 ra :=
  writeSuccessTraceTail (writeSuccess101dcTrace3 ra).
Definition writeSuccess101dcTrace5 ra :=
  subst_trace (Val_Bits (Z_to_bv 64 0x101dc)) 4
    (writeSuccessTraceTail (writeSuccess101dcTrace4 ra)).
Definition writeSuccess101dcTrace6 ra :=
  writeSuccessTraceTail (writeSuccess101dcTrace5 ra).
Definition writeSuccess101dcTrace7 ra :=
  subst_trace (Val_Bits (Z_to_bv 64 0x101dc + BV 64 4)%bv) 5
    (writeSuccessTraceTail (writeSuccess101dcTrace6 ra)).
Definition writeSuccess101dcTrace8 ra :=
  writeSuccessTraceTail (writeSuccess101dcTrace7 ra).
Definition writeSuccess101dcTrace9 ra :=
  subst_trace (Val_Bits (writeSuccess101dcTarget ra)) 7
    (writeSuccessTraceTail (writeSuccess101dcTrace8 ra)).
Definition writeSuccess101dcTrace10 ra :=
  subst_trace (Val_Bits (writeSuccess101dcTargetBit ra)) 8
    (writeSuccessTraceTail (writeSuccess101dcTrace9 ra)).
Definition writeSuccess101dcTrace11 ra :=
  writeSuccessTraceTail (writeSuccess101dcTrace10 ra).

Definition writeSuccess101dcRegs regs ra : reg_map :=
  <["PC" := RVal_Bits (writeSuccess101dcTarget ra)]> regs.
Definition writeSuccess101dcBefore regs global : IslaState :=
  (writeSuccess15694Local a101dc regs, global).
Definition writeSuccess101dcDone regs global ra : IslaState :=
  (writeSuccess15694Local tnil (writeSuccess101dcRegs regs ra), global).
Definition writeSuccess101dcAfter regs global ra : IslaState :=
  match global.(seq_instrs) !! writeSuccess101dcTarget ra with
  | Some trace =>
      (writeSuccess15694Local trace (writeSuccess101dcRegs regs ra), global)
  | None =>
      ((writeSuccess15694Local tnil (writeSuccess101dcRegs regs ra))
        <| seq_nb_state := true |>, global)
  end.
Definition writeSuccess101dcDoneLabels global ra : list seq_label :=
  match global.(seq_instrs) !! writeSuccess101dcTarget ra with
  | Some _ => []
  | None => [SInstrTrap (writeSuccess101dcTarget ra)]
  end.

Definition writeSuccess101dcLocals regs ra : list seq_local_state :=
  [writeSuccess15694Local writeSuccess101dcTrace1 regs;
   writeSuccess15694Local writeSuccess101dcTrace2 regs;
   writeSuccess15694Local (writeSuccess101dcTrace3 ra) regs;
   writeSuccess15694Local (writeSuccess101dcTrace4 ra) regs;
   writeSuccess15694Local (writeSuccess101dcTrace5 ra) regs;
   writeSuccess15694Local (writeSuccess101dcTrace6 ra) regs;
   writeSuccess15694Local (writeSuccess101dcTrace7 ra) regs;
   writeSuccess15694Local (writeSuccess101dcTrace8 ra) regs;
   writeSuccess15694Local (writeSuccess101dcTrace9 ra) regs;
   writeSuccess15694Local (writeSuccess101dcTrace10 ra) regs;
   writeSuccess15694Local (writeSuccess101dcTrace11 ra)
     (writeSuccess101dcRegs regs ra)].
Definition writeSuccess101dcPrefixObservations regs global ra :=
  map (fun local => writeSuccess15694Observation local global)
    (writeSuccess101dcLocals regs ra).
Definition writeSuccess101dcObservations regs global ra :=
  writeSuccess101dcPrefixObservations regs global ra ++
  [({| microLabels := writeSuccess101dcDoneLabels global ra;
       microAfter := writeSuccess101dcAfter regs global ra |})].

Definition writeSuccess101dcPrefix8Observations regs global ra :=
  firstn 8 (writeSuccess101dcPrefixObservations regs global ra).
Definition writeSuccess101dcTailObservations regs global ra :=
  [writeSuccess15694Observation
     (writeSuccess15694Local (writeSuccess101dcTrace9 ra) regs) global;
   writeSuccess15694Observation
     (writeSuccess15694Local (writeSuccess101dcTrace10 ra) regs) global;
   writeSuccess15694Observation
     (writeSuccess15694Local (writeSuccess101dcTrace11 ra)
       (writeSuccess101dcRegs regs ra)) global;
   ({| microLabels := writeSuccess101dcDoneLabels global ra;
       microAfter := writeSuccess101dcAfter regs global ra |})].

Lemma writeSuccess101dcObservationsSplit regs global ra :
  writeSuccess101dcObservations regs global ra =
    writeSuccess101dcPrefix8Observations regs global ra ++
    writeSuccess101dcTailObservations regs global ra.
Proof. reflexivity. Qed.

Lemma segment_101dc regs global (ra : bv 64) :
  regs !! "PC" = Some (RVal_Bits (Z_to_bv 64 0x101dc)) ->
  regs !! "x1" = Some (RVal_Bits ra) ->
  global.(seq_instrs) !! Z_to_bv 64 0x101dc = Some a101dc ->
  eval_a_exp regs writeSuccess15694Mstatus = Some (Val_Bool true) ->
  eval_a_exp regs writeSuccess101dcAlignment = Some (Val_Bool true) ->
  IslaInstructionSegment (writeSuccess101dcBefore regs global)
    (writeSuccess101dcObservations regs global ra)
    (writeSuccess101dcAfter regs global ra) /\
  (writeSuccess101dcAfter regs global ra).2.(seq_mem) = global.(seq_mem).
Proof.
  intros Hpc Hx1 Hcode Hmstatus Halign.
  assert (Hprefix : IslaInstructionPrefixPath
    (writeSuccess101dcBefore regs global)
    (writeSuccess101dcPrefixObservations regs global ra)
    (writeSuccess101dcDone regs global ra)).
  {
    unfold writeSuccess101dcPrefixObservations,
    writeSuccess101dcLocals; cbn.
    eapply IslaInstructionPrefixStep; first discriminate.
    {
    apply writeSuccessSeqSilent; first reflexivity;
    unfold writeSuccess101dcBefore, writeSuccess101dcTrace1,
      writeSuccessTraceTail, a101dc; cbn;
    apply DeclareConstBitVecS' with (b := BV 64 0).
    }
    eapply IslaInstructionPrefixStep; first discriminate.
    {
    apply writeSuccessSeqAssume; first reflexivity;
    unfold writeSuccess101dcTrace1, writeSuccessTraceTail, a101dc;
    cbn; apply AssumeS; exact Hmstatus.
    }
    eapply IslaInstructionPrefixStep; first discriminate.
    {
    apply writeSuccessSeqSilent; first reflexivity;
    unfold writeSuccess101dcTrace2, writeSuccess101dcTrace1,
      writeSuccessTraceTail, a101dc; cbn;
    apply DeclareConstBitVecS' with (b := ra).
    }
    eapply IslaInstructionPrefixStep; first discriminate.
    {
    apply writeSuccessSeqAssume; first reflexivity;
    unfold writeSuccess101dcTrace3, writeSuccess101dcTrace2,
      writeSuccess101dcTrace1, writeSuccessTraceTail, a101dc;
    cbn; apply AssumeS; exact Halign.
    }
    eapply IslaInstructionPrefixStep; first discriminate.
    {
    apply writeSuccessSeqSilent; first reflexivity;
    unfold writeSuccess101dcTrace4, writeSuccess101dcTrace3,
      writeSuccess101dcTrace2, writeSuccess101dcTrace1,
      writeSuccessTraceTail, a101dc; cbn;
    apply DeclareConstBitVecS' with (b := Z_to_bv 64 0x101dc).
    }
    eapply IslaInstructionPrefixStep; first discriminate.
    {
    eapply writeSuccessSeqReadReg with
      (root := RVal_Bits (Z_to_bv 64 0x101dc))
      (value := RVal_Bits (Z_to_bv 64 0x101dc));
    [reflexivity|unfold writeSuccess101dcTrace5,
      writeSuccess101dcTrace4, writeSuccess101dcTrace3,
      writeSuccess101dcTrace2, writeSuccess101dcTrace1,
      writeSuccessTraceTail, a101dc; cbn; constructor
    |exact Hpc|reflexivity|reflexivity].
    }
    eapply IslaInstructionPrefixStep; first discriminate.
    {
    apply writeSuccessSeqSilent; first reflexivity;
    unfold writeSuccess101dcTrace6, writeSuccess101dcTrace5,
      writeSuccess101dcTrace4, writeSuccess101dcTrace3,
      writeSuccess101dcTrace2, writeSuccess101dcTrace1,
      writeSuccessTraceTail, a101dc; cbn;
    eapply DefineConstS with
      (v := Val_Bits (Z_to_bv 64 0x101dc + BV 64 4)%bv); reflexivity.
    }
    eapply IslaInstructionPrefixStep; first discriminate.
    {
    eapply writeSuccessSeqReadReg with
      (root := RVal_Bits ra) (value := RVal_Bits ra);
    [reflexivity|unfold writeSuccess101dcTrace7,
      writeSuccess101dcTrace6, writeSuccess101dcTrace5,
      writeSuccess101dcTrace4, writeSuccess101dcTrace3,
      writeSuccess101dcTrace2, writeSuccess101dcTrace1,
      writeSuccessTraceTail, a101dc; cbn; constructor
    |exact Hx1|reflexivity|reflexivity].
    }
    eapply IslaInstructionPrefixStep; first discriminate.
    {
    apply writeSuccessSeqSilent; first reflexivity;
    unfold writeSuccess101dcTrace8, writeSuccess101dcTrace7,
      writeSuccess101dcTrace6, writeSuccess101dcTrace5,
      writeSuccess101dcTrace4, writeSuccess101dcTrace3,
      writeSuccess101dcTrace2, writeSuccess101dcTrace1,
      writeSuccess101dcTarget, writeSuccessTraceTail, a101dc; cbn;
    eapply DefineConstS with
      (v := Val_Bits (writeSuccess101dcTarget ra)); reflexivity.
    }
    eapply IslaInstructionPrefixStep; first discriminate.
    {
    apply writeSuccessSeqSilent; first reflexivity;
    unfold writeSuccess101dcTrace9, writeSuccess101dcTrace8,
      writeSuccess101dcTrace7, writeSuccess101dcTrace6,
      writeSuccess101dcTrace5, writeSuccess101dcTrace4,
      writeSuccess101dcTrace3, writeSuccess101dcTrace2,
      writeSuccess101dcTrace1, writeSuccess101dcTargetBit,
      writeSuccess101dcTarget, writeSuccessTraceTail, a101dc; cbn;
    eapply DefineConstS with
      (v := Val_Bits (writeSuccess101dcTargetBit ra)); reflexivity.
    }
    eapply IslaInstructionPrefixStep; first discriminate.
    {
    eapply writeSuccessSeqWriteReg with
      (root := RVal_Bits (Z_to_bv 64 0x101dc))
      (value := RVal_Bits (writeSuccess101dcTarget ra))
      (updated := RVal_Bits (writeSuccess101dcTarget ra));
    [reflexivity|unfold writeSuccess101dcTrace10,
      writeSuccess101dcTrace9, writeSuccess101dcTrace8,
      writeSuccess101dcTrace7, writeSuccess101dcTrace6,
      writeSuccess101dcTrace5, writeSuccess101dcTrace4,
      writeSuccess101dcTrace3, writeSuccess101dcTrace2,
      writeSuccess101dcTrace1, writeSuccessTraceTail, a101dc;
      cbn; constructor|exact Hpc|reflexivity|reflexivity].
    }
    apply IslaInstructionPrefixRefl.
  }
  destruct (global.(seq_instrs) !! writeSuccess101dcTarget ra)
    as [targetTrace|] eqn:Htarget.
  - split.
    + unfold writeSuccess101dcObservations,
        writeSuccess101dcDoneLabels, writeSuccess101dcAfter.
      rewrite Htarget.
      eapply islaInstructionSegmentIntro with
        (done := writeSuccess101dcDone regs global ra)
        (labels := []) (spawned := []).
      * split; first reflexivity.
        exists (Z_to_bv 64 0x101dc), a101dc.
        cbn. rewrite Hpc Hcode. repeat split; reflexivity.
      * exact Hprefix.
      * reflexivity.
      * unfold writeSuccess101dcDone, writeSuccess101dcRegs.
        apply writeSuccessSeqDoneTabled with
          (next := targetTrace) (trace := targetTrace); try reflexivity; try constructor.
        exists (writeSuccess101dcTarget ra). rewrite lookup_insert Htarget.
        repeat split; reflexivity.
      * left.
        split; first reflexivity.
        exists (writeSuccess101dcTarget ra), targetTrace.
        unfold writeSuccess101dcRegs. cbn. rewrite lookup_insert Htarget.
        repeat split; reflexivity.
    + unfold writeSuccess101dcAfter. rewrite Htarget. reflexivity.
  - split.
    + unfold writeSuccess101dcObservations,
        writeSuccess101dcDoneLabels, writeSuccess101dcAfter.
      rewrite Htarget.
      eapply islaInstructionSegmentIntro with
        (done := writeSuccess101dcDone regs global ra)
        (labels := [SInstrTrap (writeSuccess101dcTarget ra)])
        (spawned := []).
      * split; first reflexivity.
        exists (Z_to_bv 64 0x101dc), a101dc.
        cbn. rewrite Hpc Hcode. repeat split; reflexivity.
      * exact Hprefix.
      * reflexivity.
      * unfold writeSuccess101dcDone, writeSuccess101dcRegs.
        apply writeSuccessSeqDoneTrap with
          (next := tnil) (pc := writeSuccess101dcTarget ra);
          try reflexivity; try constructor.
        -- rewrite lookup_insert. reflexivity.
        -- exact Htarget.
      * right. reflexivity.
    + unfold writeSuccess101dcAfter. rewrite Htarget. reflexivity.
Qed.

Lemma writeSuccess101dcRegsLookupOther regs ra reg :
  reg <> "PC" -> writeSuccess101dcRegs regs ra !! reg = regs !! reg.
Proof. intros Hne. unfold writeSuccess101dcRegs. by rewrite lookup_insert_ne. Qed.

Lemma writeSuccess101dcRegsDom regs ra :
  regs !! "PC" = Some (RVal_Bits (Z_to_bv 64 0x101dc)) ->
  dom (writeSuccess101dcRegs regs ra) = dom regs.
Proof.
  intros Hpc. apply elem_of_dom_2 in Hpc. unfold writeSuccess101dcRegs.
  rewrite dom_insert_L. set_solver.
Qed.

Print Assumptions segment_101dc.
Print Assumptions writeSuccess101dcRegsLookupOther.
Print Assumptions writeSuccess101dcRegsDom.
