From Coq Require Import Lists.List ZArith.ZArith.
Require Import isla.riscv64.riscv64.
Require Import IslaTraces.write_success_90.a156a0.
Require Import IslaTraces.write_success_90.a156a4.
Require Import ZesuSsz.Contracts.InstructionBoundary.
Require Import ZesuSsz.Experiments.WriteSuccessSegmentAutomation.
Require Import ZesuSsz.Experiments.WriteSuccessCoverageAutomation.
Require Import ZesuSsz.Experiments.WriteSuccessSegment15694.

Import ListNotations.
Open Scope Z_scope.

Definition writeSuccess156a0Trace1 :=
  subst_trace (Val_Bits (BV 64 0)) 2 (writeSuccessTraceTail a156a0).
Definition writeSuccess156a0Trace2 := writeSuccessTraceTail writeSuccess156a0Trace1.
Definition writeSuccess156a0Trace3 :=
  subst_trace (Val_Bits (Z_to_bv 64 0x156a0)) 3
    (writeSuccessTraceTail writeSuccess156a0Trace2).
Definition writeSuccess156a0Trace4 := writeSuccessTraceTail writeSuccess156a0Trace3.
Definition writeSuccess156a0NextPc : bv 64 :=
  (Z_to_bv 64 0x156a0 + BV 64 4)%bv.
Definition writeSuccess156a0Trace5 :=
  subst_trace (Val_Bits writeSuccess156a0NextPc) 4
    (writeSuccessTraceTail writeSuccess156a0Trace4).
Definition writeSuccess156a0Link : bv 64 :=
  (Z_to_bv 64 0x156a0 + BV 64 0xffffffffffffb000)%bv.
Definition writeSuccess156a0Trace6 :=
  subst_trace (Val_Bits writeSuccess156a0Link) 5
    (writeSuccessTraceTail writeSuccess156a0Trace5).
Definition writeSuccess156a0Trace7 := writeSuccessTraceTail writeSuccess156a0Trace6.
Definition writeSuccess156a0Trace8 := writeSuccessTraceTail writeSuccess156a0Trace7.

Definition writeSuccess156a0Regs (regs : reg_map) : reg_map :=
  <["PC" := RVal_Bits writeSuccess156a0NextPc]>
    (<["x1" := RVal_Bits writeSuccess156a0Link]> regs).

Lemma writeSuccess156a0RegsLookupOther regs reg :
  reg <> "PC" ->
  reg <> "x1" ->
  writeSuccess156a0Regs regs !! reg = regs !! reg.
Proof.
  intros Hpc Hx12. unfold writeSuccess156a0Regs.
  rewrite lookup_insert_ne; last congruence.
  rewrite lookup_insert_ne; last congruence.
  reflexivity.
Qed.

Lemma writeSuccess156a0RegsDom regs oldX1 :
  regs !! "PC" = Some (RVal_Bits (Z_to_bv 64 0x156a0)) ->
  regs !! "x1" = Some oldX1 ->
  dom (writeSuccess156a0Regs regs) = dom regs.
Proof.
  intros Hpc Hx12.
  apply elem_of_dom_2 in Hpc. apply elem_of_dom_2 in Hx12.
  unfold writeSuccess156a0Regs. rewrite !dom_insert_L.
  set_solver.
Qed.

Definition writeSuccess156a0Before (regs : reg_map)
    (global : seq_global_state) : IslaState :=
  (writeSuccess15694Local a156a0 regs, global).

Definition writeSuccess156a0After (regs : reg_map)
    (global : seq_global_state) : IslaState :=
  (writeSuccess15694Local a156a4 (writeSuccess156a0Regs regs), global).

Lemma writeSuccess156a0NextPcExact :
  writeSuccess156a0NextPc = Z_to_bv 64 0x156a4.
Proof. unfold writeSuccess156a0NextPc. bv_solve. Qed.

Definition writeSuccess156a0PrefixObservations (regs : reg_map)
    (global : seq_global_state) : list IslaMicroObservation :=
  [writeSuccess15694Observation
     (writeSuccess15694Local writeSuccess156a0Trace1 regs) global;
   writeSuccess15694Observation
     (writeSuccess15694Local writeSuccess156a0Trace2 regs) global;
   writeSuccess15694Observation
     (writeSuccess15694Local writeSuccess156a0Trace3 regs) global;
   writeSuccess15694Observation
     (writeSuccess15694Local writeSuccess156a0Trace4 regs) global;
   writeSuccess15694Observation
     (writeSuccess15694Local writeSuccess156a0Trace5 regs) global;
   writeSuccess15694Observation
     (writeSuccess15694Local writeSuccess156a0Trace6 regs) global;
   writeSuccess15694Observation
     (writeSuccess15694Local writeSuccess156a0Trace7
       (<["x1" := RVal_Bits writeSuccess156a0Link]> regs)) global;
   writeSuccess15694Observation
     (writeSuccess15694Local writeSuccess156a0Trace8
       (writeSuccess156a0Regs regs)) global].

Definition writeSuccess156a0Observations (regs : reg_map)
    (global : seq_global_state) : list IslaMicroObservation :=
  writeSuccess156a0PrefixObservations regs global ++
  [writeSuccess15694Observation
     (writeSuccess156a0After regs global).1 global].

Lemma segment_156a0_mstatus (regs : reg_map) (global : seq_global_state) oldX1 :
  regs !! "PC" = Some (RVal_Bits (Z_to_bv 64 0x156a0)) ->
  regs !! "x1" = Some oldX1 ->
  global.(seq_instrs) !! Z_to_bv 64 0x156a0 = Some a156a0 ->
  global.(seq_instrs) !! Z_to_bv 64 0x156a4 = Some a156a4 ->
  eval_a_exp regs writeSuccess15694Mstatus = Some (Val_Bool true) ->
  IslaInstructionSegment (writeSuccess156a0Before regs global)
    (writeSuccess156a0Observations regs global)
    (writeSuccess156a0After regs global) /\
  (writeSuccess156a0After regs global).1.(seq_regs) =
    writeSuccess156a0Regs regs /\
  (writeSuccess156a0After regs global).2.(seq_mem) = global.(seq_mem) /\
  concat (map microLabels (writeSuccess156a0Observations regs global)) = [].
Proof.
  intros Hpc Hx12 Hcode Hnext Hmstatus.
  split; [|repeat split; reflexivity].
  unfold writeSuccess156a0Observations.
  eapply islaInstructionSegmentIntro with
    (done := (writeSuccess15694Local tnil (writeSuccess156a0Regs regs), global))
    (labels := []) (spawned := []).
  - split; first reflexivity. exists (Z_to_bv 64 0x156a0), a156a0.
    cbn. rewrite Hpc Hcode. repeat split; reflexivity.
  - unfold writeSuccess156a0PrefixObservations.
    eapply IslaInstructionPrefixStep; first discriminate.
    { apply writeSuccessSeqSilent; first reflexivity.
      unfold writeSuccess156a0Before, writeSuccess156a0Trace1,
        writeSuccessTraceTail, a156a0. cbn.
      apply DeclareConstBitVecS' with (b := BV 64 0). }
    eapply IslaInstructionPrefixStep; first discriminate.
    { apply writeSuccessSeqAssume; first reflexivity.
      unfold writeSuccess156a0Trace1, writeSuccessTraceTail, a156a0. cbn.
      eapply AssumeS. exact Hmstatus. }
    eapply IslaInstructionPrefixStep; first discriminate.
    { apply writeSuccessSeqSilent; first reflexivity.
      unfold writeSuccess156a0Trace2, writeSuccess156a0Trace1,
        writeSuccessTraceTail, a156a0. cbn.
      apply DeclareConstBitVecS' with (b := Z_to_bv 64 0x156a0). }
    eapply IslaInstructionPrefixStep; first discriminate.
    { eapply writeSuccessSeqReadReg with
        (root := RVal_Bits (Z_to_bv 64 0x156a0))
        (value := RVal_Bits (Z_to_bv 64 0x156a0)).
      - reflexivity.
      - unfold writeSuccess156a0Trace3, writeSuccess156a0Trace2,
          writeSuccess156a0Trace1, writeSuccessTraceTail, a156a0. cbn.
        constructor.
      - exact Hpc.
      - reflexivity.
      - reflexivity. }
    eapply IslaInstructionPrefixStep; first discriminate.
    { apply writeSuccessSeqSilent; first reflexivity.
      unfold writeSuccess156a0Trace5, writeSuccess156a0Trace4,
        writeSuccess156a0Trace3, writeSuccess156a0Trace2,
        writeSuccess156a0Trace1, writeSuccess156a0NextPc,
        writeSuccessTraceTail, a156a0. cbn.
      eapply DefineConstS with
        (v := Val_Bits (Z_to_bv 64 0x156a0 + BV 64 4)%bv).
      reflexivity. }
    eapply IslaInstructionPrefixStep; first discriminate.
    { apply writeSuccessSeqSilent; first reflexivity.
      unfold writeSuccess156a0Trace5, writeSuccess156a0Trace4,
        writeSuccess156a0Trace3, writeSuccess156a0Trace2,
        writeSuccess156a0Trace1, writeSuccess156a0Link,
        writeSuccessTraceTail, a156a0. cbn.
      eapply DefineConstS with
        (v := Val_Bits
          (Z_to_bv 64 0x156a0 + BV 64 0xffffffffffffb000)%bv).
      reflexivity. }
    eapply IslaInstructionPrefixStep; first discriminate.
    { eapply writeSuccessSeqWriteReg with (root := oldX1)
        (value := RVal_Bits writeSuccess156a0Link)
        (updated := RVal_Bits writeSuccess156a0Link).
      - reflexivity.
      - unfold writeSuccess156a0Trace6, writeSuccess156a0Trace5,
          writeSuccess156a0Link, writeSuccess156a0Trace4,
          writeSuccess156a0Trace3, writeSuccess156a0Trace2,
          writeSuccess156a0Trace1, writeSuccessTraceTail, a156a0. cbn.
        constructor.
      - exact Hx12.
      - reflexivity.
      - reflexivity. }
    eapply IslaInstructionPrefixStep; first discriminate.
    { eapply writeSuccessSeqWriteReg with
        (root := RVal_Bits (Z_to_bv 64 0x156a0))
        (value := RVal_Bits writeSuccess156a0NextPc)
        (updated := RVal_Bits writeSuccess156a0NextPc).
      - reflexivity.
      - unfold writeSuccess156a0Trace7, writeSuccess156a0Trace6,
          writeSuccess156a0Trace5,
          writeSuccess156a0Trace4, writeSuccess156a0Trace3,
          writeSuccess156a0Trace2, writeSuccess156a0Trace1,
          writeSuccessTraceTail, a156a0. cbn. constructor.
      - rewrite lookup_insert_ne; last done. exact Hpc.
      - reflexivity.
      - reflexivity. }
    apply IslaInstructionPrefixRefl.
  - reflexivity.
  - apply writeSuccessSeqDoneTabled with (next := a156a4) (trace := a156a4).
    + reflexivity.
    + reflexivity.
    + constructor.
    + exists (Z_to_bv 64 0x156a4).
      unfold writeSuccess156a0Regs. rewrite lookup_insert.
      rewrite writeSuccess156a0NextPcExact Hnext.
      repeat split; reflexivity.
  - left. split; first reflexivity. exists (Z_to_bv 64 0x156a4), a156a4.
    cbn. unfold writeSuccess156a0Regs. rewrite lookup_insert.
    rewrite writeSuccess156a0NextPcExact Hnext.
    repeat split; reflexivity.
Qed.

Lemma segment_156a0 (regs : reg_map) (global : seq_global_state) oldX1 :
  regs !! "PC" = Some (RVal_Bits (Z_to_bv 64 0x156a0)) ->
  regs !! "x1" = Some oldX1 ->
  global.(seq_instrs) !! Z_to_bv 64 0x156a0 = Some a156a0 ->
  global.(seq_instrs) !! Z_to_bv 64 0x156a4 = Some a156a4 ->
  eval_a_exp regs writeSuccess15694Mstatus = Some (Val_Bool true) ->
  IslaInstructionSegment (writeSuccess156a0Before regs global)
    (writeSuccess156a0Observations regs global)
    (writeSuccess156a0After regs global) /\
  (writeSuccess156a0After regs global).1.(seq_regs) =
    writeSuccess156a0Regs regs /\
  (writeSuccess156a0After regs global).2.(seq_mem) = global.(seq_mem) /\
  concat (map microLabels (writeSuccess156a0Observations regs global)) = [].
Proof.
  intros Hpc Hx12 Hcode Hnext Hmstatus.
  eapply segment_156a0_mstatus; eauto.
Qed.

Print Assumptions segment_156a0_mstatus.
Print Assumptions segment_156a0.
Print Assumptions writeSuccess156a0RegsLookupOther.
Print Assumptions writeSuccess156a0RegsDom.

Lemma segment_156a0_mstatus_covered (regs : reg_map) (global : seq_global_state)
    oldX1 observations after :
  regs !! "PC" = Some (RVal_Bits (Z_to_bv 64 0x156a0)) ->
  regs !! "x1" = Some oldX1 ->
  global.(seq_instrs) !! Z_to_bv 64 0x156a0 = Some a156a0 ->
  global.(seq_instrs) !! Z_to_bv 64 0x156a4 = Some a156a4 ->
  eval_a_exp regs writeSuccess15694Mstatus = Some (Val_Bool true) ->
  IslaInstructionSegment (writeSuccess156a0Before regs global)
    observations after ->
  after = writeSuccess156a0After regs global /\
  observations = writeSuccess156a0Observations regs global.
Proof.
  intros Hpc Hx12 Hcode Hnext Hmstatus Hsegment.
  destruct Hsegment as
    [Hstart done prefix labels spawned Hprefix Hnil Hdone Hobservations Hend].
  have HdoneNb := seqStepSourceBlocking _ _ _ _ _ _ Hdone.
  destruct (writeSuccess15694TakeStep _ _ _ Hprefix
    ltac:(unfold writeSuccess156a0Before, writeSuccess15694Local, a156a0;
      discriminate) Hnil HdoneNb) as
    (labels0 & local1 & global1 & spawned0 & prefix1 &
     Hobs0 & Hstep0 & Hnb1 & Hprefix1).
  pose (before1 := (local1, global1)).
  inversion Hstep0 as [? ? ? ? ? ? ? Hnb0 Htrace0 Hsem0]; subst.
  unfold writeSuccess156a0Before, writeSuccess15694Local, a156a0 in Htrace0.
  cbn in Htrace0. inversion Htrace0; subst. cbn in Hsem0.
  destruct Hsem0 as (-> & -> & ->).

  destruct (writeSuccess15694TakeStep _ _ _ Hprefix1
    ltac:(unfold before1; cbn; discriminate) Hnil HdoneNb) as
    (labels1 & local2 & global2 & spawned1 & prefix2 &
     Hobs1 & Hstep1 & Hnb2 & Hprefix2).
  pose (before2 := (local2, global2)).
  eapply writeSuccessAssumeCovered in Hstep1.
  2: reflexivity.
  2: exact Hmstatus.
  destruct Hstep1 as (-> & -> & -> & ->).

  destruct (writeSuccess15694TakeStep _ _ _ Hprefix2
    ltac:(unfold before2; cbn; discriminate) Hnil HdoneNb) as
    (labels2 & local3 & global3 & spawned2 & prefix3 &
     Hobs2 & Hstep2 & Hnb3 & Hprefix3).
  pose (before3 := (local3, global3)).
  inversion Hstep2 as [? ? ? ? ? ? ? Hnb2' Htrace2 Hsem2]; subst.
  unfold before2, writeSuccess156a0Trace2, writeSuccess156a0Trace1,
    writeSuccessTraceTail, a156a0 in Htrace2. cbn in Htrace2.
  inversion Htrace2; subst. cbn in Hsem2.
  destruct Hsem2 as (-> & -> & ->).

  destruct (writeSuccess15694TakeStep _ _ _ Hprefix3
    ltac:(unfold before3; cbn; discriminate) Hnil HdoneNb) as
    (labels3 & local4 & global4 & spawned3 & prefix4 &
     Hobs3 & Hstep3 & Hnb4 & Hprefix4).
  pose (before4 := (local4, global4)).
  eapply writeSuccessReadRegCovered in Hstep3.
  2: reflexivity.
  2: exact Hpc.
  2: reflexivity.
  2: exact Hnb4.
  destruct Hstep3 as (-> & -> & -> & -> & HsymbolicPc).
  cbn in HsymbolicPc. inversion HsymbolicPc as [HpcValue].
  assert (HpcBits : @BV 64 n0 Heq0 = Z_to_bv 64 0x156a0).
  { apply bv_eq. cbn. exact HpcValue. }
  repeat match goal with
  | H : context [@BV 64 n0 Heq0] |- _ => rewrite HpcBits in H
  end.

  destruct (writeSuccess15694TakeStep _ _ _ Hprefix4
    ltac:(cbn; discriminate) Hnil HdoneNb) as
    (labels4 & local5 & global5 & spawned4 & prefix5 &
     Hobs4 & Hstep4 & Hnb5 & Hprefix5).
  pose (before5 := (local5, global5)).
  eapply writeSuccessDefineConstCovered in Hstep4.
  2: reflexivity.
  2: reflexivity.
  destruct Hstep4 as (-> & -> & -> & ->).

  destruct (writeSuccess15694TakeStep _ _ _ Hprefix5
    ltac:(cbn; discriminate) Hnil HdoneNb) as
    (labels5 & local6 & global6 & spawned5 & prefix6 &
     Hobs5 & Hstep5 & Hnb6 & Hprefix6).
  pose (before6 := (local6, global6)).
  eapply writeSuccessDefineConstCovered in Hstep5.
  2: reflexivity.
  2: reflexivity.
  destruct Hstep5 as (-> & -> & -> & ->).

  destruct (writeSuccess15694TakeStep _ _ _ Hprefix6
    ltac:(cbn; discriminate) Hnil HdoneNb) as
    (labels6 & local7 & global7 & spawned6 & prefix7 &
     Hobs6 & Hstep6 & Hnb7 & Hprefix7).
  pose (before7 := (local7, global7)).
  eapply writeSuccessWriteRegCovered in Hstep6.
  2: reflexivity.
  2: exact Hx12.
  2: reflexivity.
  2: reflexivity.
  destruct Hstep6 as (-> & -> & -> & ->).

  destruct (writeSuccess15694TakeStep _ _ _ Hprefix7
    ltac:(cbn; discriminate) Hnil HdoneNb) as
    (labels7 & local8 & global8 & spawned7 & prefix8 &
     Hobs7 & Hstep7 & Hnb8 & Hprefix8).
  eapply writeSuccessWriteRegCovered in Hstep7.
  2: reflexivity.
  2: rewrite lookup_insert_ne; last done; exact Hpc.
  2: reflexivity.
  2: reflexivity.
  destruct Hstep7 as (-> & -> & -> & ->).

  inversion Hprefix8; subst.
  2: contradiction.
  eapply writeSuccessDoneTabledCovered in Hdone.
  2: reflexivity.
  2: { unfold writeSuccess156a0Regs. rewrite lookup_insert. reflexivity. }
  2: exact Hnext.
  destruct Hdone as (Hlabels & HafterLocal & HafterGlobal & Hspawned).
  subst labels spawned.
  destruct after as [afterLocal afterGlobal].
  cbn in HafterLocal, HafterGlobal, Hend |- *.
  subst afterLocal afterGlobal.
  split.
  - reflexivity.
  - unfold writeSuccess156a0Observations,
      writeSuccess156a0PrefixObservations.
    cbn in *.
    fold writeSuccess156a0NextPc.
    rewrite HpcBits.
    reflexivity.
Qed.

Lemma segment_156a0_covered (regs : reg_map) (global : seq_global_state)
    oldX1 observations after :
  regs !! "PC" = Some (RVal_Bits (Z_to_bv 64 0x156a0)) ->
  regs !! "x1" = Some oldX1 ->
  global.(seq_instrs) !! Z_to_bv 64 0x156a0 = Some a156a0 ->
  global.(seq_instrs) !! Z_to_bv 64 0x156a4 = Some a156a4 ->
  eval_a_exp regs writeSuccess15694Mstatus = Some (Val_Bool true) ->
  IslaInstructionSegment (writeSuccess156a0Before regs global)
    observations after ->
  after = writeSuccess156a0After regs global /\
  observations = writeSuccess156a0Observations regs global.
Proof.
  intros Hpc Hx12 Hcode Hnext Hmstatus Hsegment.
  eapply segment_156a0_mstatus_covered; eauto.
Qed.

Print Assumptions segment_156a0_mstatus_covered.
Print Assumptions segment_156a0_covered.
