From Coq Require Import Lists.List ZArith.ZArith.
Require Import isla.riscv64.riscv64.
Require Import IslaTraces.write_success_02.a101e0.
Require Import IslaTraces.write_success_02.a101e4.
Require Import ZesuSsz.Contracts.InstructionBoundary.
Require Import ZesuSsz.Experiments.WriteSuccessSegmentAutomation.
Require Import ZesuSsz.Experiments.WriteSuccessCoverageAutomation.
Require Import ZesuSsz.Experiments.WriteSuccessSegment15694.

Import ListNotations.
Open Scope Z_scope.

Definition writeSuccess101e0NextPc : bv 64 :=
  (Z_to_bv 64 0x101e0 + BV 64 4)%bv.
Definition writeSuccess101e0Trace1 :=
  subst_trace (Val_Bits (BV 64 0)) 2 (writeSuccessTraceTail a101e0).
Definition writeSuccess101e0Trace2 := writeSuccessTraceTail writeSuccess101e0Trace1.
Definition writeSuccess101e0Trace3 :=
  subst_trace (Val_Bits (Z_to_bv 64 0x101e0)) 3
    (writeSuccessTraceTail writeSuccess101e0Trace2).
Definition writeSuccess101e0Trace4 := writeSuccessTraceTail writeSuccess101e0Trace3.
Definition writeSuccess101e0Trace5 :=
  subst_trace (Val_Bits writeSuccess101e0NextPc) 4
    (writeSuccessTraceTail writeSuccess101e0Trace4).
Definition writeSuccess101e0Trace6 (left : bv 64) :=
  subst_trace (Val_Bits left) 5 (writeSuccessTraceTail writeSuccess101e0Trace5).
Definition writeSuccess101e0Trace7 left :=
  writeSuccessTraceTail (writeSuccess101e0Trace6 left).
Definition writeSuccess101e0Trace8 (left right : bv 64) :=
  subst_trace (Val_Bits right) 6
    (writeSuccessTraceTail (writeSuccess101e0Trace7 left)).
Definition writeSuccess101e0Trace9 left right :=
  writeSuccessTraceTail (writeSuccess101e0Trace8 left right).
Definition writeSuccess101e0Trace10 (left right : bv 64) :=
  subst_trace (Val_Bits (left + right)%bv) 7
    (writeSuccessTraceTail (writeSuccess101e0Trace9 left right)).
Definition writeSuccess101e0Trace11 left right :=
  writeSuccessTraceTail (writeSuccess101e0Trace10 left right).
Definition writeSuccess101e0Trace12 left right :=
  writeSuccessTraceTail (writeSuccess101e0Trace11 left right).

Definition writeSuccess101e0Regs regs (left right : bv 64) : reg_map :=
  <["PC" := RVal_Bits writeSuccess101e0NextPc]>
    (<["x13" := RVal_Bits (left + right)%bv]> regs).
Definition writeSuccess101e0Before regs global : IslaState :=
  (writeSuccess15694Local a101e0 regs, global).
Definition writeSuccess101e0After regs global (left right : bv 64) : IslaState :=
  (writeSuccess15694Local a101e4
    (writeSuccess101e0Regs regs left right), global).

Lemma writeSuccess101e0NextPcExact :
  writeSuccess101e0NextPc = Z_to_bv 64 0x101e4.
Proof. vm_compute. apply bv_eq. reflexivity. Qed.

Definition writeSuccess101e0Locals regs (left right : bv 64) :=
  [writeSuccess15694Local writeSuccess101e0Trace1 regs;
   writeSuccess15694Local writeSuccess101e0Trace2 regs;
   writeSuccess15694Local writeSuccess101e0Trace3 regs;
   writeSuccess15694Local writeSuccess101e0Trace4 regs;
   writeSuccess15694Local writeSuccess101e0Trace5 regs;
   writeSuccess15694Local (writeSuccess101e0Trace6 left) regs;
   writeSuccess15694Local (writeSuccess101e0Trace7 left) regs;
   writeSuccess15694Local (writeSuccess101e0Trace8 left right) regs;
   writeSuccess15694Local (writeSuccess101e0Trace9 left right) regs;
   writeSuccess15694Local (writeSuccess101e0Trace10 left right) regs;
   writeSuccess15694Local (writeSuccess101e0Trace11 left right)
     (<["x13" := RVal_Bits (left + right)%bv]> regs);
   writeSuccess15694Local (writeSuccess101e0Trace12 left right)
     (writeSuccess101e0Regs regs left right)].
Definition writeSuccess101e0PrefixObservations regs global
    (left right : bv 64) :=
  map (fun local => writeSuccess15694Observation local global)
    (writeSuccess101e0Locals regs left right).
Definition writeSuccess101e0Observations regs global (left right : bv 64) :=
  writeSuccess101e0PrefixObservations regs global left right ++
  [writeSuccess15694Observation
    (writeSuccess101e0After regs global left right).1 global].

Lemma writeSuccess101e0RegsLookupOther regs left right reg :
  reg <> "PC" -> reg <> "x13" ->
  writeSuccess101e0Regs regs left right !! reg = regs !! reg.
Proof. intros Hpc Hdest. unfold writeSuccess101e0Regs.
  rewrite lookup_insert_ne; last congruence.
  rewrite lookup_insert_ne; last congruence. reflexivity. Qed.

Lemma writeSuccess101e0RegsDom regs left right oldX13 :
  regs !! "PC" = Some (RVal_Bits (Z_to_bv 64 0x101e0)) ->
  regs !! "x13" = Some oldX13 ->
  dom (writeSuccess101e0Regs regs left right) = dom regs.
Proof. intros Hpc Hdest. apply elem_of_dom_2 in Hpc.
  apply elem_of_dom_2 in Hdest. unfold writeSuccess101e0Regs.
  rewrite !dom_insert_L. set_solver. Qed.

Lemma writeSuccess101e0PrefixPath regs global (left right : bv 64) oldX13 :
  regs !! "PC" = Some (RVal_Bits (Z_to_bv 64 0x101e0)) ->
  regs !! "x11" = Some (RVal_Bits left) ->
  regs !! "x15" = Some (RVal_Bits right) ->
  regs !! "x13" = Some oldX13 ->
  eval_a_exp regs writeSuccess15694Mstatus = Some (Val_Bool true) ->
  IslaInstructionPrefixPath (writeSuccess101e0Before regs global)
    (writeSuccess101e0PrefixObservations regs global left right)
    (writeSuccess15694Local tnil
      (writeSuccess101e0Regs regs left right), global).
Proof.
  intros Hpc Hleft Hright Hdest Hmstatus.
  unfold writeSuccess101e0PrefixObservations, writeSuccess101e0Locals.
  eapply IslaInstructionPrefixStep; first discriminate.
  { apply writeSuccessSeqSilent; first reflexivity. unfold writeSuccess101e0Before,
      writeSuccess101e0Trace1, writeSuccessTraceTail, a101e0. cbn.
    apply DeclareConstBitVecS' with (b := BV 64 0). }
  eapply IslaInstructionPrefixStep; first discriminate.
  { apply writeSuccessSeqAssume; first reflexivity. unfold writeSuccess101e0Trace1,
      writeSuccessTraceTail, a101e0. cbn. eapply AssumeS. exact Hmstatus. }
  eapply IslaInstructionPrefixStep; first discriminate.
  { apply writeSuccessSeqSilent; first reflexivity.
    unfold writeSuccess101e0Trace2, writeSuccess101e0Trace1,
      writeSuccessTraceTail, a101e0. cbn.
    apply DeclareConstBitVecS' with (b := Z_to_bv 64 0x101e0). }
  eapply IslaInstructionPrefixStep; first discriminate.
  { eapply writeSuccessSeqReadReg with
      (root := RVal_Bits (Z_to_bv 64 0x101e0))
      (value := RVal_Bits (Z_to_bv 64 0x101e0)).
    - reflexivity.
    - unfold writeSuccess101e0Trace3, writeSuccess101e0Trace2,
        writeSuccess101e0Trace1, writeSuccessTraceTail, a101e0. cbn. constructor.
    - exact Hpc. - reflexivity. - reflexivity. }
  eapply IslaInstructionPrefixStep; first discriminate.
  { apply writeSuccessSeqSilent; first reflexivity.
    cbn [writeSuccess101e0Trace4 writeSuccess101e0Trace3
      writeSuccess101e0Trace2 writeSuccess101e0Trace1
      writeSuccess101e0NextPc writeSuccessTraceTail a101e0].
    eapply DefineConstS with (v := Val_Bits writeSuccess101e0NextPc). reflexivity. }
  eapply IslaInstructionPrefixStep; first discriminate.
  { apply writeSuccessSeqSilent; first reflexivity. cbn [writeSuccess101e0Trace5
      writeSuccess101e0Trace4 writeSuccess101e0Trace3 writeSuccess101e0Trace2
      writeSuccess101e0Trace1 writeSuccess101e0NextPc writeSuccessTraceTail a101e0].
    apply DeclareConstBitVecS' with (b := left). }
  eapply IslaInstructionPrefixStep; first discriminate.
  { eapply writeSuccessSeqReadReg with (root := RVal_Bits left)
      (value := RVal_Bits left).
    - reflexivity.
    - cbn [writeSuccess101e0Trace6 writeSuccess101e0Trace5
        writeSuccess101e0Trace4 writeSuccess101e0Trace3
        writeSuccess101e0Trace2 writeSuccess101e0Trace1
        writeSuccess101e0NextPc writeSuccessTraceTail a101e0]. constructor.
    - exact Hleft. - reflexivity. - reflexivity. }
  eapply IslaInstructionPrefixStep; first discriminate.
  { apply writeSuccessSeqSilent; first reflexivity.
    cbn [writeSuccess101e0Trace7 writeSuccess101e0Trace6
      writeSuccess101e0Trace5 writeSuccess101e0Trace4
      writeSuccess101e0Trace3 writeSuccess101e0Trace2
      writeSuccess101e0Trace1 writeSuccess101e0NextPc
      writeSuccessTraceTail a101e0].
    apply DeclareConstBitVecS' with (b := right). }
  eapply IslaInstructionPrefixStep; first discriminate.
  { eapply writeSuccessSeqReadReg with (root := RVal_Bits right)
      (value := RVal_Bits right).
    - reflexivity.
    - cbn [writeSuccess101e0Trace8 writeSuccess101e0Trace7
        writeSuccess101e0Trace6 writeSuccess101e0Trace5
        writeSuccess101e0Trace4 writeSuccess101e0Trace3
        writeSuccess101e0Trace2 writeSuccess101e0Trace1
        writeSuccess101e0NextPc writeSuccessTraceTail a101e0]. constructor.
    - exact Hright. - reflexivity. - reflexivity. }
  eapply IslaInstructionPrefixStep; first discriminate.
  { apply writeSuccessSeqSilent; first reflexivity.
    cbn [writeSuccess101e0Trace9 writeSuccess101e0Trace8
      writeSuccess101e0Trace7 writeSuccess101e0Trace6
      writeSuccess101e0Trace5 writeSuccess101e0Trace4
      writeSuccess101e0Trace3 writeSuccess101e0Trace2
      writeSuccess101e0Trace1 writeSuccess101e0NextPc
      writeSuccessTraceTail a101e0].
    eapply DefineConstS with (v := Val_Bits (left + right)%bv). reflexivity. }
  eapply IslaInstructionPrefixStep; first discriminate.
  { eapply writeSuccessSeqWriteReg with (root := oldX13)
      (value := RVal_Bits (left + right)%bv)
      (updated := RVal_Bits (left + right)%bv).
    - reflexivity.
    - cbn [writeSuccess101e0Trace10 writeSuccess101e0Trace9
        writeSuccess101e0Trace8 writeSuccess101e0Trace7
        writeSuccess101e0Trace6 writeSuccess101e0Trace5
        writeSuccess101e0Trace4 writeSuccess101e0Trace3
        writeSuccess101e0Trace2 writeSuccess101e0Trace1
        writeSuccess101e0NextPc writeSuccessTraceTail a101e0]. constructor.
    - exact Hdest. - reflexivity. - reflexivity. }
  eapply IslaInstructionPrefixStep; first discriminate.
  { eapply writeSuccessSeqWriteReg with
      (root := RVal_Bits (Z_to_bv 64 0x101e0))
      (value := RVal_Bits writeSuccess101e0NextPc)
      (updated := RVal_Bits writeSuccess101e0NextPc).
    - reflexivity.
    - cbn [writeSuccess101e0Trace11 writeSuccess101e0Trace10
        writeSuccess101e0Trace9 writeSuccess101e0Trace8
        writeSuccess101e0Trace7 writeSuccess101e0Trace6
        writeSuccess101e0Trace5 writeSuccess101e0Trace4
        writeSuccess101e0Trace3 writeSuccess101e0Trace2
        writeSuccess101e0Trace1 writeSuccess101e0NextPc
        writeSuccessTraceTail a101e0]. constructor.
    - rewrite lookup_insert_ne; last done. exact Hpc.
    - reflexivity. - reflexivity. }
  apply IslaInstructionPrefixRefl.
Qed.

Lemma segment_101e0_mstatus regs global (left right : bv 64) oldX13 :
  regs !! "PC" = Some (RVal_Bits (Z_to_bv 64 0x101e0)) ->
  regs !! "x11" = Some (RVal_Bits left) ->
  regs !! "x15" = Some (RVal_Bits right) ->
  regs !! "x13" = Some oldX13 ->
  global.(seq_instrs) !! Z_to_bv 64 0x101e0 = Some a101e0 ->
  global.(seq_instrs) !! Z_to_bv 64 0x101e4 = Some a101e4 ->
  eval_a_exp regs writeSuccess15694Mstatus = Some (Val_Bool true) ->
  IslaInstructionSegment (writeSuccess101e0Before regs global)
    (writeSuccess101e0Observations regs global left right)
    (writeSuccess101e0After regs global left right) /\
  (writeSuccess101e0After regs global left right).1.(seq_regs) =
    writeSuccess101e0Regs regs left right /\
  (writeSuccess101e0After regs global left right).2.(seq_mem) = global.(seq_mem) /\
  concat (map microLabels
    (writeSuccess101e0Observations regs global left right)) = [].
Proof.
  intros Hpc Hleft Hright Hdest Hcode Hnext Hmstatus.
  split; [|repeat split; reflexivity].
  unfold writeSuccess101e0Observations.
  eapply islaInstructionSegmentIntro with
    (done := (writeSuccess15694Local tnil
      (writeSuccess101e0Regs regs left right), global))
    (labels := []) (spawned := []).
  - split; first reflexivity. exists (Z_to_bv 64 0x101e0), a101e0.
    cbn. rewrite Hpc Hcode. repeat split; reflexivity.
  - eapply writeSuccess101e0PrefixPath; eauto.
  - reflexivity.
  - apply writeSuccessSeqDoneTabled with (next := a101e4) (trace := a101e4).
    + reflexivity. + reflexivity. + constructor.
    + exists (Z_to_bv 64 0x101e4). unfold writeSuccess101e0Regs.
      rewrite lookup_insert. rewrite writeSuccess101e0NextPcExact Hnext.
      repeat split; reflexivity.
  - left. split; first reflexivity. exists (Z_to_bv 64 0x101e4), a101e4.
    cbn. unfold writeSuccess101e0Regs. rewrite lookup_insert.
    rewrite writeSuccess101e0NextPcExact Hnext. repeat split; reflexivity.
Qed.

Lemma segment_101e0 regs global (left right : bv 64) oldX13 :
  regs !! "PC" = Some (RVal_Bits (Z_to_bv 64 0x101e0)) ->
  regs !! "x11" = Some (RVal_Bits left) ->
  regs !! "x15" = Some (RVal_Bits right) ->
  regs !! "x13" = Some oldX13 ->
  global.(seq_instrs) !! Z_to_bv 64 0x101e0 = Some a101e0 ->
  global.(seq_instrs) !! Z_to_bv 64 0x101e4 = Some a101e4 ->
  eval_a_exp regs writeSuccess15694Mstatus = Some (Val_Bool true) ->
  IslaInstructionSegment (writeSuccess101e0Before regs global)
    (writeSuccess101e0Observations regs global left right)
    (writeSuccess101e0After regs global left right) /\
  (writeSuccess101e0After regs global left right).1.(seq_regs) =
    writeSuccess101e0Regs regs left right /\
  (writeSuccess101e0After regs global left right).2.(seq_mem) = global.(seq_mem) /\
  concat (map microLabels
    (writeSuccess101e0Observations regs global left right)) = [].
Proof.
  intros Hpc Hleft Hright Hdest Hcode Hnext Hmstatus.
  eapply segment_101e0_mstatus; eauto.
Qed.

Print Assumptions writeSuccess101e0PrefixPath.
Print Assumptions segment_101e0_mstatus.
Print Assumptions segment_101e0.
Print Assumptions writeSuccess101e0RegsLookupOther.
Print Assumptions writeSuccess101e0RegsDom.
