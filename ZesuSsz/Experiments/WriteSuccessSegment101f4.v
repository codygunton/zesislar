From Coq Require Import Lists.List ZArith.ZArith.
Require Import isla.riscv64.riscv64.
Require Import IslaTraces.write_success_02.a101d8.
Require Import IslaTraces.write_success_02.a101f4.
Require Import ZesuSsz.Contracts.InstructionBoundary.
Require Import ZesuSsz.Experiments.WriteSuccessSegmentAutomation.
Require Import ZesuSsz.Experiments.WriteSuccessCoverageAutomation.
Require Import ZesuSsz.Experiments.WriteSuccessTraceAssumptions.
Require Import ZesuSsz.Experiments.WriteSuccessSegment15694.

Import ListNotations.
Open Scope Z_scope.

Definition writeSuccess101f4Alignment : a_exp :=
  AExp_Binop Eq
    (AExp_Unop (Extract 1 0) (AExp_Val (AVal_Var "PC" []) Mk_annot) Mk_annot)
    (AExp_Val (AVal_Bits (BV 2 0)) Mk_annot) Mk_annot.

Lemma writeSuccess101f4AlignmentHolds regs :
  regs !! "PC" = Some (RVal_Bits (Z_to_bv 64 0x101f4)) ->
  eval_a_exp regs writeSuccess101f4Alignment = Some (Val_Bool true).
Proof.
  intros Hpc. unfold writeSuccess101f4Alignment. cbn. rewrite Hpc. vm_compute.
  reflexivity.
Qed.

Definition writeSuccess101f4NextPc : bv 64 :=
  (Z_to_bv 64 0x101f4 + BV 64 4)%bv.
Definition writeSuccess101f4TargetPc : bv 64 :=
  (Z_to_bv 64 0x101f4 + BV 64 0xffffffffffffffe4)%bv.
Definition writeSuccess101f4TargetBit : bv 1 :=
  bv_extract 0 1 (bv_shiftr writeSuccess101f4TargetPc (BV 64 1)).

Definition writeSuccess101f4Trace1 :=
  subst_trace (Val_Bits (BV 64 0)) 2 (writeSuccessTraceTail a101f4).
Definition writeSuccess101f4Trace2 := writeSuccessTraceTail writeSuccess101f4Trace1.
Definition writeSuccess101f4Trace3 :=
  subst_trace (Val_Bits (Z_to_bv 64 0x101f4)) 3
    (writeSuccessTraceTail writeSuccess101f4Trace2).
Definition writeSuccess101f4Trace4 := writeSuccessTraceTail writeSuccess101f4Trace3.
Definition writeSuccess101f4Trace5 := writeSuccessTraceTail writeSuccess101f4Trace4.
Definition writeSuccess101f4Trace6 :=
  subst_trace (Val_Bits writeSuccess101f4NextPc) 4
    (writeSuccessTraceTail writeSuccess101f4Trace5).
Definition writeSuccess101f4Trace7 :=
  subst_trace (Val_Bits writeSuccess101f4TargetPc) 5
    (writeSuccessTraceTail writeSuccess101f4Trace6).
Definition writeSuccess101f4Trace8 :=
  subst_trace (Val_Bits writeSuccess101f4TargetBit) 6
    (writeSuccessTraceTail writeSuccess101f4Trace7).
Definition writeSuccess101f4Trace9 := writeSuccessTraceTail writeSuccess101f4Trace8.

Definition writeSuccess101f4Regs regs : reg_map :=
  <["PC" := RVal_Bits writeSuccess101f4TargetPc]> regs.
Definition writeSuccess101f4Before regs global : IslaState :=
  (writeSuccess15694Local a101f4 regs, global).
Definition writeSuccess101f4After regs global : IslaState :=
  (writeSuccess15694Local a101d8 (writeSuccess101f4Regs regs), global).

Lemma writeSuccess101f4TargetExact :
  writeSuccess101f4TargetPc = Z_to_bv 64 0x101d8.
Proof. vm_compute. apply bv_eq. reflexivity. Qed.

Lemma writeSuccess101f4RegsLookupOther regs reg :
  reg <> "PC" -> writeSuccess101f4Regs regs !! reg = regs !! reg.
Proof. intros Hreg. unfold writeSuccess101f4Regs.
  rewrite lookup_insert_ne; last congruence. reflexivity. Qed.

Lemma writeSuccess101f4RegsDom regs :
  regs !! "PC" = Some (RVal_Bits (Z_to_bv 64 0x101f4)) ->
  dom (writeSuccess101f4Regs regs) = dom regs.
Proof. intros Hpc. apply elem_of_dom_2 in Hpc.
  unfold writeSuccess101f4Regs. rewrite dom_insert_L. set_solver. Qed.

Definition writeSuccess101f4PrefixObservations regs global :=
  map (fun trace => writeSuccess15694Observation
    (writeSuccess15694Local trace regs) global)
    [writeSuccess101f4Trace1; writeSuccess101f4Trace2;
     writeSuccess101f4Trace3; writeSuccess101f4Trace4;
     writeSuccess101f4Trace5; writeSuccess101f4Trace6;
     writeSuccess101f4Trace7; writeSuccess101f4Trace8] ++
  [writeSuccess15694Observation
    (writeSuccess15694Local writeSuccess101f4Trace9
      (writeSuccess101f4Regs regs)) global].
Definition writeSuccess101f4Observations regs global :=
  writeSuccess101f4PrefixObservations regs global ++
  [writeSuccess15694Observation (writeSuccess101f4After regs global).1 global].

Lemma segment_101f4_mstatus regs global :
  regs !! "PC" = Some (RVal_Bits (Z_to_bv 64 0x101f4)) ->
  global.(seq_instrs) !! Z_to_bv 64 0x101f4 = Some a101f4 ->
  global.(seq_instrs) !! Z_to_bv 64 0x101d8 = Some a101d8 ->
  eval_a_exp regs writeSuccess15694Mstatus = Some (Val_Bool true) ->
  IslaInstructionSegment (writeSuccess101f4Before regs global)
    (writeSuccess101f4Observations regs global)
    (writeSuccess101f4After regs global) /\
  (writeSuccess101f4After regs global).1.(seq_regs) =
    writeSuccess101f4Regs regs /\
  (writeSuccess101f4After regs global).2.(seq_mem) = global.(seq_mem) /\
  concat (map microLabels (writeSuccess101f4Observations regs global)) = [].
Proof.
  intros Hpc Hcode Hnext Hmstatus. split; [|repeat split; reflexivity].
  have Halign := writeSuccess101f4AlignmentHolds regs Hpc.
  unfold writeSuccess101f4Observations, writeSuccess101f4PrefixObservations.
  eapply islaInstructionSegmentIntro with
    (done := (writeSuccess15694Local tnil (writeSuccess101f4Regs regs), global))
    (labels := []) (spawned := []).
  - split; first reflexivity. exists (Z_to_bv 64 0x101f4), a101f4.
    cbn. rewrite Hpc Hcode. repeat split; reflexivity.
  - eapply IslaInstructionPrefixStep; first discriminate.
    { apply writeSuccessSeqSilent; first reflexivity.
      unfold writeSuccess101f4Before, writeSuccess101f4Trace1,
        writeSuccessTraceTail, a101f4. cbn.
      apply DeclareConstBitVecS' with (b := BV 64 0). }
    eapply IslaInstructionPrefixStep; first discriminate.
    { apply writeSuccessSeqAssume; first reflexivity.
      unfold writeSuccess101f4Trace1, writeSuccessTraceTail, a101f4. cbn.
      eapply AssumeS. exact Hmstatus. }
    eapply IslaInstructionPrefixStep; first discriminate.
    { apply writeSuccessSeqSilent; first reflexivity.
      unfold writeSuccess101f4Trace2, writeSuccess101f4Trace1,
        writeSuccessTraceTail, a101f4. cbn.
      apply DeclareConstBitVecS' with (b := Z_to_bv 64 0x101f4). }
    eapply IslaInstructionPrefixStep; first discriminate.
    { apply writeSuccessSeqAssume; first reflexivity.
      unfold writeSuccess101f4Trace3, writeSuccess101f4Trace2,
        writeSuccess101f4Trace1, writeSuccessTraceTail, a101f4. cbn.
      eapply AssumeS. exact Halign. }
    eapply IslaInstructionPrefixStep; first discriminate.
    { eapply writeSuccessSeqReadReg with
        (root := RVal_Bits (Z_to_bv 64 0x101f4))
        (value := RVal_Bits (Z_to_bv 64 0x101f4)).
      - reflexivity.
      - unfold writeSuccess101f4Trace4, writeSuccess101f4Trace3,
          writeSuccess101f4Trace2, writeSuccess101f4Trace1,
          writeSuccessTraceTail, a101f4. cbn. constructor.
      - exact Hpc. - reflexivity. - reflexivity. }
    eapply IslaInstructionPrefixStep; first discriminate.
    { apply writeSuccessSeqSilent; first reflexivity.
      cbn [writeSuccess101f4Trace5 writeSuccess101f4Trace4
        writeSuccess101f4Trace3 writeSuccess101f4Trace2
        writeSuccess101f4Trace1 writeSuccess101f4NextPc
        writeSuccessTraceTail a101f4].
      eapply DefineConstS with (v := Val_Bits writeSuccess101f4NextPc).
      reflexivity. }
    eapply IslaInstructionPrefixStep; first discriminate.
    { apply writeSuccessSeqSilent; first reflexivity.
      cbn [writeSuccess101f4Trace6 writeSuccess101f4Trace5
        writeSuccess101f4Trace4 writeSuccess101f4Trace3
        writeSuccess101f4Trace2 writeSuccess101f4Trace1
        writeSuccess101f4NextPc writeSuccess101f4TargetPc
        writeSuccessTraceTail a101f4].
      eapply DefineConstS with (v := Val_Bits writeSuccess101f4TargetPc).
      reflexivity. }
    eapply IslaInstructionPrefixStep; first discriminate.
    { apply writeSuccessSeqSilent; first reflexivity.
      cbn [writeSuccess101f4Trace7 writeSuccess101f4Trace6
        writeSuccess101f4Trace5 writeSuccess101f4Trace4
        writeSuccess101f4Trace3 writeSuccess101f4Trace2
        writeSuccess101f4Trace1 writeSuccess101f4NextPc
        writeSuccess101f4TargetPc writeSuccess101f4TargetBit
        writeSuccessTraceTail a101f4].
      eapply DefineConstS with (v := Val_Bits writeSuccess101f4TargetBit).
      reflexivity. }
    eapply IslaInstructionPrefixStep; first discriminate.
    { eapply writeSuccessSeqWriteReg with
        (root := RVal_Bits (Z_to_bv 64 0x101f4))
        (value := RVal_Bits writeSuccess101f4TargetPc)
        (updated := RVal_Bits writeSuccess101f4TargetPc).
      - reflexivity.
      - cbn [writeSuccess101f4Trace8 writeSuccess101f4Trace7
          writeSuccess101f4Trace6 writeSuccess101f4Trace5
          writeSuccess101f4Trace4 writeSuccess101f4Trace3
          writeSuccess101f4Trace2 writeSuccess101f4Trace1
          writeSuccess101f4NextPc writeSuccess101f4TargetPc
          writeSuccess101f4TargetBit writeSuccessTraceTail a101f4]. constructor.
      - exact Hpc. - reflexivity. - reflexivity. }
    apply IslaInstructionPrefixRefl.
  - reflexivity.
  - apply writeSuccessSeqDoneTabled with (next := a101d8) (trace := a101d8).
    + reflexivity. + reflexivity. + constructor.
    + exists (Z_to_bv 64 0x101d8). unfold writeSuccess101f4Regs.
      rewrite lookup_insert. rewrite writeSuccess101f4TargetExact Hnext.
      repeat split; reflexivity.
  - left. split; first reflexivity. exists (Z_to_bv 64 0x101d8), a101d8.
    cbn. unfold writeSuccess101f4Regs. rewrite lookup_insert.
    rewrite writeSuccess101f4TargetExact Hnext. repeat split; reflexivity.
Qed.

Lemma segment_101f4 regs global :
  regs !! "PC" = Some (RVal_Bits (Z_to_bv 64 0x101f4)) ->
  global.(seq_instrs) !! Z_to_bv 64 0x101f4 = Some a101f4 ->
  global.(seq_instrs) !! Z_to_bv 64 0x101d8 = Some a101d8 ->
  writeSuccessTraceAssumptions (writeSuccess101f4Before regs global) ->
  IslaInstructionSegment (writeSuccess101f4Before regs global)
    (writeSuccess101f4Observations regs global)
    (writeSuccess101f4After regs global) /\
  (writeSuccess101f4After regs global).1.(seq_regs) =
    writeSuccess101f4Regs regs /\
  (writeSuccess101f4After regs global).2.(seq_mem) = global.(seq_mem) /\
  concat (map microLabels (writeSuccess101f4Observations regs global)) = [].
Proof.
  intros Hpc Hcode Hnext Hassumptions. eapply segment_101f4_mstatus; eauto.
  exact (writeSuccess15694MstatusFromTraceAssumptions regs global Hassumptions).
Qed.

Print Assumptions writeSuccess101f4AlignmentHolds.
Print Assumptions writeSuccess101f4TargetExact.
Print Assumptions writeSuccess101f4RegsLookupOther.
Print Assumptions writeSuccess101f4RegsDom.
Print Assumptions segment_101f4_mstatus.
Print Assumptions segment_101f4.
