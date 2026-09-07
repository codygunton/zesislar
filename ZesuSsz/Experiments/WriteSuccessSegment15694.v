From Coq Require Import Eqdep_dec Lists.List ZArith.ZArith.
Require Import isla.riscv64.riscv64.
Require Import IslaTraces.write_success_90.a15694.
Require Import IslaTraces.write_success_90.a15698.
Require Import ZesuSsz.Contracts.InstructionBoundary.
Require Import ZesuSsz.Experiments.WriteSuccessSegmentAutomation.
Require Import ZesuSsz.Experiments.WriteSuccessCoverageAutomation.
Require Import ZesuSsz.Experiments.WriteSuccessTraceAssumptions.
Require Import ZesuSsz.Experiments.WriteSuccessTraceAssumptionsChunk00.
Require Import ZesuSsz.Experiments.WriteSuccessTraceAssumptionsChunk01.
Require Import ZesuSsz.Experiments.WriteSuccessTraceAssumptionsChunk02.
Require Import ZesuSsz.Experiments.WriteSuccessTraceAssumptionsChunk03.
Require Import ZesuSsz.Experiments.WriteSuccessTraceAssumptionsChunk04.
Require Import ZesuSsz.Experiments.WriteSuccessTraceAssumptionsChunk05.
Require Import ZesuSsz.Experiments.WriteSuccessTraceAssumptionsChunk06.
Require Import ZesuSsz.Experiments.WriteSuccessTraceAssumptionsChunk07.
Require Import ZesuSsz.Experiments.WriteSuccessTraceAssumptionsChunk08.
Require Import ZesuSsz.Experiments.WriteSuccessTraceAssumptionsChunk09.
Require Import ZesuSsz.Experiments.WriteSuccessTraceAssumptionsChunk10.
Require Import ZesuSsz.Experiments.WriteSuccessTraceAssumptionsChunk11.
Require Import ZesuSsz.Experiments.WriteSuccessTraceAssumptionsChunk12.
Require Import ZesuSsz.Experiments.WriteSuccessTraceAssumptionsChunk13.
Require Import ZesuSsz.Experiments.WriteSuccessTraceAssumptionsChunk14.
Require Import ZesuSsz.Experiments.WriteSuccessTraceAssumptionsChunk15.
Require Import ZesuSsz.Experiments.WriteSuccessTraceAssumptionsChunk16.

Import ListNotations.
Open Scope Z_scope.

Definition writeSuccessTraceTail (trace : isla_trace) : isla_trace :=
  match trace with tcons _ rest => rest | _ => tnil end.

Definition writeSuccess15694Mstatus : a_exp :=
  AExp_Binop Eq
    (AExp_Manyop (Bvmanyarith Bvand)
      [AExp_Val (AVal_Var "mstatus" [Field "bits"]) Mk_annot;
       AExp_Val (AVal_Bits (BV 64 0x20000)) Mk_annot] Mk_annot)
    (AExp_Val (AVal_Bits (BV 64 0)) Mk_annot) Mk_annot.

Definition writeSuccess15694Trace1 :=
  subst_trace (Val_Bits (BV 64 0)) 2 (writeSuccessTraceTail a15694).
Definition writeSuccess15694Trace2 := writeSuccessTraceTail writeSuccess15694Trace1.
Definition writeSuccess15694Trace3 :=
  subst_trace (Val_Bits (Z_to_bv 64 0x15694)) 3
    (writeSuccessTraceTail writeSuccess15694Trace2).
Definition writeSuccess15694Trace4 := writeSuccessTraceTail writeSuccess15694Trace3.
Definition writeSuccess15694NextPc : bv 64 :=
  (Z_to_bv 64 0x15694 + BV 64 4)%bv.
Definition writeSuccess15694Trace5 :=
  subst_trace (Val_Bits writeSuccess15694NextPc) 4
    (writeSuccessTraceTail writeSuccess15694Trace4).
Definition writeSuccess15694Trace6 (sp : bv 64) :=
  subst_trace (Val_Bits sp) 5 (writeSuccessTraceTail writeSuccess15694Trace5).
Definition writeSuccess15694Trace7 (sp : bv 64) :=
  writeSuccessTraceTail (writeSuccess15694Trace6 sp).
Definition writeSuccess15694Trace8 (sp : bv 64) :=
  subst_trace (Val_Bits (sp + BV 64 1744)%bv) 6
    (writeSuccessTraceTail (writeSuccess15694Trace7 sp)).
Definition writeSuccess15694Trace9 (sp : bv 64) :=
  writeSuccessTraceTail (writeSuccess15694Trace8 sp).
Definition writeSuccess15694Trace10 (sp : bv 64) :=
  writeSuccessTraceTail (writeSuccess15694Trace9 sp).

Definition writeSuccess15694Regs (regs : reg_map) (sp : bv 64) : reg_map :=
  <["PC" := RVal_Bits writeSuccess15694NextPc]>
    (<["x10" := RVal_Bits (sp + BV 64 1744)%bv]> regs).

Lemma writeSuccess15694RegsLookupOther regs sp reg :
  reg <> "PC" ->
  reg <> "x10" ->
  writeSuccess15694Regs regs sp !! reg = regs !! reg.
Proof.
  intros Hpc Hx10. unfold writeSuccess15694Regs.
  rewrite lookup_insert_ne; last congruence.
  rewrite lookup_insert_ne; last congruence.
  reflexivity.
Qed.

Definition writeSuccess15694Local (trace : isla_trace) (regs : reg_map) :
    seq_local_state := {|
  seq_trace := trace;
  seq_regs := regs;
  seq_pc_reg := "PC";
  seq_nb_state := false
|}.

Definition writeSuccess15694Before (regs : reg_map)
    (global : seq_global_state) : IslaState :=
  (writeSuccess15694Local a15694 regs, global).

Definition writeSuccess15694After (regs : reg_map) (global : seq_global_state)
    (sp : bv 64) : IslaState :=
  (writeSuccess15694Local a15698 (writeSuccess15694Regs regs sp), global).

Definition writeSuccess15694Observation (local : seq_local_state)
    (global : seq_global_state) : IslaMicroObservation := {|
  microLabels := [];
  microAfter := (local, global)
|}.

Lemma writeSuccess15694NextPcExact :
  writeSuccess15694NextPc = Z_to_bv 64 0x15698.
Proof. unfold writeSuccess15694NextPc. bv_solve. Qed.

Definition writeSuccess15694PrefixObservations (regs : reg_map)
    (global : seq_global_state) (sp : bv 64) : list IslaMicroObservation :=
  [writeSuccess15694Observation
     (writeSuccess15694Local writeSuccess15694Trace1 regs) global;
   writeSuccess15694Observation
     (writeSuccess15694Local writeSuccess15694Trace2 regs) global;
   writeSuccess15694Observation
     (writeSuccess15694Local writeSuccess15694Trace3 regs) global;
   writeSuccess15694Observation
     (writeSuccess15694Local writeSuccess15694Trace4 regs) global;
   writeSuccess15694Observation
     (writeSuccess15694Local writeSuccess15694Trace5 regs) global;
   writeSuccess15694Observation
     (writeSuccess15694Local (writeSuccess15694Trace6 sp) regs) global;
   writeSuccess15694Observation
     (writeSuccess15694Local (writeSuccess15694Trace7 sp) regs) global;
   writeSuccess15694Observation
     (writeSuccess15694Local (writeSuccess15694Trace8 sp) regs) global;
   writeSuccess15694Observation
     (writeSuccess15694Local (writeSuccess15694Trace9 sp)
       (<["x10" := RVal_Bits (sp + BV 64 1744)%bv]> regs)) global;
   writeSuccess15694Observation
     (writeSuccess15694Local (writeSuccess15694Trace10 sp)
       (writeSuccess15694Regs regs sp)) global].

Definition writeSuccess15694Observations (regs : reg_map)
    (global : seq_global_state) (sp : bv 64) : list IslaMicroObservation :=
  writeSuccess15694PrefixObservations regs global sp ++
  [writeSuccess15694Observation
     (writeSuccess15694After regs global sp).1 global].

Lemma writeSuccess15694MstatusFromTraceAssumptions regs global :
  writeSuccessTraceAssumptions (writeSuccess15694Before regs global) ->
  eval_a_exp regs writeSuccess15694Mstatus = Some (Val_Bool true).
Proof.
  intros Hassumptions.
  apply Forall_forall with
    (x := Assume writeSuccess15694Mstatus Mk_annot :t: tnil)
    in Hassumptions.
  - exact Hassumptions.
  - unfold writeSuccessTraceAssumptionEvents.
    rewrite elem_of_list_In.
    apply in_concat. exists writeSuccessTraceAssumptionsChunk11.
    split.
    + cbn. tauto.
    + unfold writeSuccessTraceAssumptionsChunk11,
        writeSuccess15694Mstatus. cbn. tauto.
Qed.

Lemma writeSuccess15694TakeStep before observations done :
  IslaInstructionPrefixPath before observations done ->
  before.1.(seq_trace) <> tnil ->
  done.1.(seq_trace) = tnil ->
  done.1.(seq_nb_state) = false ->
  exists labels middleLocal middleGlobal spawned rest,
    observations =
      {| microLabels := labels;
         microAfter := (middleLocal, middleGlobal) |} :: rest /\
    seq_step before.1 before.2 labels middleLocal middleGlobal spawned /\
    middleLocal.(seq_nb_state) = false /\
    IslaInstructionPrefixPath (middleLocal, middleGlobal) rest done.
Proof.
  intros Hpath Hsource HdoneTrace HdoneNb.
  exact (writeSuccessInstructionPrefixTakeStep before observations done
    Hsource HdoneTrace HdoneNb Hpath).
Qed.

Lemma segment_15694 (regs : reg_map) (global : seq_global_state)
    (sp : bv 64) oldX10 :
  regs !! "PC" = Some (RVal_Bits (Z_to_bv 64 0x15694)) ->
  regs !! "x2" = Some (RVal_Bits sp) ->
  regs !! "x10" = Some oldX10 ->
  global.(seq_instrs) !! Z_to_bv 64 0x15694 = Some a15694 ->
  global.(seq_instrs) !! Z_to_bv 64 0x15698 = Some a15698 ->
  writeSuccessTraceAssumptions (writeSuccess15694Before regs global) ->
  IslaInstructionSegment (writeSuccess15694Before regs global)
    (writeSuccess15694Observations regs global sp)
    (writeSuccess15694After regs global sp) /\
  (writeSuccess15694After regs global sp).1.(seq_regs) =
    writeSuccess15694Regs regs sp /\
  (writeSuccess15694After regs global sp).2.(seq_mem) = global.(seq_mem) /\
  concat (map microLabels (writeSuccess15694Observations regs global sp)) = [].
Proof.
  intros Hpc Hsp Hx10 Hcode Hnext Hassumptions.
  have Hmstatus := writeSuccess15694MstatusFromTraceAssumptions
    regs global Hassumptions.
  split; [|repeat split; reflexivity].
  unfold writeSuccess15694Observations.
  eapply islaInstructionSegmentIntro with
    (done := (writeSuccess15694Local tnil (writeSuccess15694Regs regs sp), global))
    (labels := []) (spawned := []).
  - split; first reflexivity. exists (Z_to_bv 64 0x15694), a15694.
    cbn. rewrite Hpc Hcode. repeat split; reflexivity.
  - unfold writeSuccess15694PrefixObservations.
    eapply IslaInstructionPrefixStep; first discriminate.
    { apply writeSuccessSeqSilent; first reflexivity.
      unfold writeSuccess15694Before, writeSuccess15694Local,
        writeSuccess15694Trace1, writeSuccessTraceTail, a15694. cbn.
      apply DeclareConstBitVecS' with (b := BV 64 0). }
    eapply IslaInstructionPrefixStep; first discriminate.
    { apply writeSuccessSeqAssume; first reflexivity.
      unfold writeSuccess15694Trace1, writeSuccessTraceTail, a15694. cbn.
      eapply AssumeS. exact Hmstatus. }
    eapply IslaInstructionPrefixStep; first discriminate.
    { apply writeSuccessSeqSilent; first reflexivity.
      unfold writeSuccess15694Trace2, writeSuccess15694Trace1,
        writeSuccessTraceTail, a15694. cbn.
      apply DeclareConstBitVecS' with (b := Z_to_bv 64 0x15694). }
    eapply IslaInstructionPrefixStep; first discriminate.
    { eapply writeSuccessSeqReadReg with
        (root := RVal_Bits (Z_to_bv 64 0x15694))
        (value := RVal_Bits (Z_to_bv 64 0x15694)).
      - reflexivity.
      - unfold writeSuccess15694Trace3, writeSuccess15694Trace2,
          writeSuccess15694Trace1, writeSuccessTraceTail, a15694. cbn.
        constructor.
      - exact Hpc.
      - reflexivity.
      - reflexivity. }
    eapply IslaInstructionPrefixStep; first discriminate.
    { apply writeSuccessSeqSilent; first reflexivity.
      unfold writeSuccess15694Trace5, writeSuccess15694Trace4, writeSuccess15694Trace3,
        writeSuccess15694Trace2, writeSuccess15694Trace1,
        writeSuccess15694NextPc, writeSuccessTraceTail, a15694. cbn.
      eapply DefineConstS with
        (v := Val_Bits (Z_to_bv 64 0x15694 + BV 64 4)%bv).
      reflexivity. }
    eapply IslaInstructionPrefixStep; first discriminate.
    { apply writeSuccessSeqSilent; first reflexivity.
      unfold writeSuccess15694Trace5, writeSuccess15694Trace4,
        writeSuccess15694Trace3, writeSuccess15694Trace2,
        writeSuccess15694Trace1, writeSuccessTraceTail, a15694. cbn.
      apply DeclareConstBitVecS' with (b := sp). }
    eapply IslaInstructionPrefixStep; first discriminate.
    { eapply writeSuccessSeqReadReg with
        (root := RVal_Bits sp) (value := RVal_Bits sp).
      - reflexivity.
      - unfold writeSuccess15694Trace6, writeSuccess15694Trace5,
          writeSuccess15694Trace4, writeSuccess15694Trace3,
          writeSuccess15694Trace2, writeSuccess15694Trace1,
          writeSuccessTraceTail, a15694. cbn. constructor.
      - exact Hsp.
      - reflexivity.
      - reflexivity. }
    eapply IslaInstructionPrefixStep; first discriminate.
    { apply writeSuccessSeqSilent; first reflexivity.
      unfold writeSuccess15694Trace7, writeSuccess15694Trace6,
        writeSuccess15694Trace5, writeSuccess15694Trace4,
        writeSuccess15694Trace3, writeSuccess15694Trace2,
        writeSuccess15694Trace1, writeSuccessTraceTail, a15694. cbn.
      eapply DefineConstS with (v := Val_Bits (sp + BV 64 1744)%bv).
      reflexivity. }
    eapply IslaInstructionPrefixStep; first discriminate.
    { eapply writeSuccessSeqWriteReg with (root := oldX10)
        (value := RVal_Bits (sp + BV 64 1744)%bv)
        (updated := RVal_Bits (sp + BV 64 1744)%bv).
      - reflexivity.
      - unfold writeSuccess15694Trace8, writeSuccess15694Trace7,
          writeSuccess15694Trace6, writeSuccess15694Trace5,
          writeSuccess15694Trace4, writeSuccess15694Trace3,
          writeSuccess15694Trace2, writeSuccess15694Trace1,
          writeSuccessTraceTail, a15694. cbn. constructor.
      - exact Hx10.
      - reflexivity.
      - reflexivity. }
    eapply IslaInstructionPrefixStep; first discriminate.
    { eapply writeSuccessSeqWriteReg with
        (root := RVal_Bits (Z_to_bv 64 0x15694))
        (value := RVal_Bits writeSuccess15694NextPc)
        (updated := RVal_Bits writeSuccess15694NextPc).
      - reflexivity.
      - unfold writeSuccess15694Trace9, writeSuccess15694Trace8,
          writeSuccess15694Trace7, writeSuccess15694Trace6,
          writeSuccess15694Trace5, writeSuccess15694Trace4,
          writeSuccess15694Trace3, writeSuccess15694Trace2,
          writeSuccess15694Trace1, writeSuccessTraceTail, a15694. cbn.
        constructor.
      - rewrite lookup_insert_ne; last done. exact Hpc.
      - reflexivity.
      - reflexivity. }
    apply IslaInstructionPrefixRefl.
  - reflexivity.
  - apply writeSuccessSeqDoneTabled with (next := a15698) (trace := a15698).
    + reflexivity.
    + reflexivity.
    + constructor.
    + exists (Z_to_bv 64 0x15698).
      unfold writeSuccess15694Regs. rewrite lookup_insert.
      rewrite writeSuccess15694NextPcExact Hnext.
      repeat split; reflexivity.
  - left. split; first reflexivity. exists (Z_to_bv 64 0x15698), a15698.
    cbn. unfold writeSuccess15694Regs. rewrite lookup_insert.
    rewrite writeSuccess15694NextPcExact Hnext.
    repeat split; reflexivity.
Qed.

Print Assumptions writeSuccess15694MstatusFromTraceAssumptions.
Print Assumptions writeSuccess15694NextPcExact.
Print Assumptions segment_15694.
Print Assumptions writeSuccess15694RegsLookupOther.

Lemma segment_15694_covered (regs : reg_map) (global : seq_global_state)
    (sp : bv 64) oldX10 observations after :
  regs !! "PC" = Some (RVal_Bits (Z_to_bv 64 0x15694)) ->
  regs !! "x2" = Some (RVal_Bits sp) ->
  regs !! "x10" = Some oldX10 ->
  global.(seq_instrs) !! Z_to_bv 64 0x15694 = Some a15694 ->
  global.(seq_instrs) !! Z_to_bv 64 0x15698 = Some a15698 ->
  writeSuccessTraceAssumptions (writeSuccess15694Before regs global) ->
  IslaInstructionSegment (writeSuccess15694Before regs global)
    observations after ->
  after = writeSuccess15694After regs global sp /\
  observations = writeSuccess15694Observations regs global sp.
Proof.
  intros Hpc Hsp Hx10 Hcode Hnext Hassumptions Hsegment.
  have Hmstatus := writeSuccess15694MstatusFromTraceAssumptions
    regs global Hassumptions.
  destruct Hsegment as
    [Hstart done prefix labels spawned Hprefix Hnil Hdone Hobservations Hend].
  have HdoneNb := seqStepSourceBlocking _ _ _ _ _ _ Hdone.
  assert (Hsource0 :
    (writeSuccess15694Before regs global).1.(seq_trace) <> tnil).
  { unfold writeSuccess15694Before, writeSuccess15694Local, a15694.
    discriminate. }
  destruct (writeSuccess15694TakeStep
    _ _ _ Hprefix Hsource0 Hnil HdoneNb) as
    (labels0 & local1 & global1 & spawned0 & prefix1 &
     Hobs0 & Hstep0 & Hnb1 & Hprefix1).
  pose (before1 := (local1, global1)).
  inversion Hstep0 as [? ? ? ? ? ? ? Hnb0 Htrace0 Hsem0]; subst.
  unfold writeSuccess15694Before, writeSuccess15694Local, a15694 in Htrace0.
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
  unfold before2, writeSuccess15694Trace2, writeSuccess15694Trace1,
    writeSuccessTraceTail, a15694 in Htrace2. cbn in Htrace2.
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
  assert (HpcBits : @BV 64 n0 Heq0 = Z_to_bv 64 0x15694).
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
  inversion Hstep5 as [? ? ? ? ? ? ? Hnb5' Htrace5 Hsem5]; subst.
  unfold before5, writeSuccess15694Trace5, writeSuccess15694Trace4,
    writeSuccess15694Trace3, writeSuccess15694Trace2,
    writeSuccess15694Trace1, writeSuccessTraceTail, a15694 in Htrace5.
  cbn in Htrace5. inversion Htrace5; subst. cbn in Hsem5.
  destruct Hsem5 as (-> & -> & ->).

  destruct (writeSuccess15694TakeStep _ _ _ Hprefix6
    ltac:(cbn; discriminate) Hnil HdoneNb) as
    (labels6 & local7 & global7 & spawned6 & prefix7 &
     Hobs6 & Hstep6 & Hnb7 & Hprefix7).
  pose (before7 := (local7, global7)).
  eapply writeSuccessReadRegCovered in Hstep6.
  2: reflexivity.
  2: exact Hsp.
  2: reflexivity.
  2: exact Hnb7.
  destruct Hstep6 as (-> & -> & -> & -> & HsymbolicSp).
  cbn in HsymbolicSp. inversion HsymbolicSp as [HspValue].
  pose proof (inj_pair2_eq_dec N (Coq.NArith.BinNat.N.eq_dec)
    (fun width => bv width) 64%N (BV 64 n0) sp HspValue) as HspBits.
  repeat match goal with
  | H : context [BV 64 n0] |- _ => rewrite HspBits in H
  end.

  destruct (writeSuccess15694TakeStep _ _ _ Hprefix7
    ltac:(cbn; discriminate) Hnil HdoneNb) as
    (labels7 & local8 & global8 & spawned7 & prefix8 &
     Hobs7 & Hstep7 & Hnb8 & Hprefix8).
  pose (before8 := (local8, global8)).
  eapply writeSuccessDefineConstCovered in Hstep7.
  2: reflexivity.
  2: reflexivity.
  destruct Hstep7 as (-> & -> & -> & ->).

  destruct (writeSuccess15694TakeStep _ _ _ Hprefix8
    ltac:(cbn; discriminate) Hnil HdoneNb) as
    (labels8 & local9 & global9 & spawned8 & prefix9 &
     Hobs8 & Hstep8 & Hnb9 & Hprefix9).
  pose (before9 := (local9, global9)).
  eapply writeSuccessWriteRegCovered in Hstep8.
  2: reflexivity.
  2: exact Hx10.
  2: reflexivity.
  2: reflexivity.
  destruct Hstep8 as (-> & -> & -> & ->).

  destruct (writeSuccess15694TakeStep _ _ _ Hprefix9
    ltac:(cbn; discriminate) Hnil HdoneNb) as
    (labels9 & local10 & global10 & spawned9 & prefix10 &
     Hobs9 & Hstep9 & Hnb10 & Hprefix10).
  eapply writeSuccessWriteRegCovered in Hstep9.
  2: reflexivity.
  2: rewrite lookup_insert_ne; last done; exact Hpc.
  2: reflexivity.
  2: reflexivity.
  destruct Hstep9 as (-> & -> & -> & ->).

  inversion Hprefix10; subst.
  2: contradiction.
  eapply writeSuccessDoneTabledCovered in Hdone.
  2: reflexivity.
  2: { unfold writeSuccess15694Regs. rewrite lookup_insert. reflexivity. }
  2: exact Hnext.
  destruct Hdone as (Hlabels & HafterLocal & HafterGlobal & Hspawned).
  subst labels spawned.
  destruct after as [afterLocal afterGlobal].
  cbn in HafterLocal, HafterGlobal, Hend |- *.
  subst afterLocal afterGlobal.
  split.
  - reflexivity.
  - unfold writeSuccess15694Observations,
      writeSuccess15694PrefixObservations.
    cbn in *.
    fold writeSuccess15694NextPc.
    rewrite HpcBits.
    reflexivity.
Qed.

Print Assumptions segment_15694_covered.
