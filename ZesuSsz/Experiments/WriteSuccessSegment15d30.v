From Coq Require Import Eqdep_dec Lists.List ZArith.ZArith.
Require Import isla.riscv64.riscv64.
Require Import IslaTraces.write_success_07.a15d30.
Require Import IslaTraces.write_success_07.a15d34.
Require Import ZesuSsz.Contracts.InstructionBoundary.
Require Import ZesuSsz.Experiments.WriteSuccessSegmentAutomation.
Require Import ZesuSsz.Experiments.WriteSuccessCoverageAutomation.

Import ListNotations.
Open Scope Z_scope.

Definition writeSuccessTraceTail (trace : isla_trace) : isla_trace :=
  match trace with tcons _ rest => rest | _ => tnil end.

Definition writeSuccess15d30Mstatus : a_exp :=
  AExp_Binop Eq
    (AExp_Manyop (Bvmanyarith Bvand)
      [AExp_Val (AVal_Var "mstatus" [Field "bits"]) Mk_annot;
       AExp_Val (AVal_Bits (BV 64 0x20000)) Mk_annot] Mk_annot)
    (AExp_Val (AVal_Bits (BV 64 0)) Mk_annot) Mk_annot.

Definition writeSuccess15d30Trace1 :=
  subst_trace (Val_Bits (BV 64 0)) 2 (writeSuccessTraceTail a15d30).
Definition writeSuccess15d30Trace2 := writeSuccessTraceTail writeSuccess15d30Trace1.
Definition writeSuccess15d30Trace3 :=
  subst_trace (Val_Bits (Z_to_bv 64 0x15d30)) 3
    (writeSuccessTraceTail writeSuccess15d30Trace2).
Definition writeSuccess15d30Trace4 := writeSuccessTraceTail writeSuccess15d30Trace3.
Definition writeSuccess15d30NextPc : bv 64 :=
  (Z_to_bv 64 0x15d30 + BV 64 4)%bv.
Definition writeSuccess15d30Trace5 :=
  subst_trace (Val_Bits writeSuccess15d30NextPc) 4
    (writeSuccessTraceTail writeSuccess15d30Trace4).
Definition writeSuccess15d30Trace6 (sp : bv 64) :=
  subst_trace (Val_Bits sp) 5 (writeSuccessTraceTail writeSuccess15d30Trace5).
Definition writeSuccess15d30Trace7 (sp : bv 64) :=
  writeSuccessTraceTail (writeSuccess15d30Trace6 sp).
Definition writeSuccess15d30Trace8 (sp : bv 64) :=
  subst_trace (Val_Bits (sp + BV 64 16)%bv) 6
    (writeSuccessTraceTail (writeSuccess15d30Trace7 sp)).
Definition writeSuccess15d30Trace9 (sp : bv 64) :=
  writeSuccessTraceTail (writeSuccess15d30Trace8 sp).
Definition writeSuccess15d30Trace10 (sp : bv 64) :=
  writeSuccessTraceTail (writeSuccess15d30Trace9 sp).

Definition writeSuccess15d30Regs (regs : reg_map) (sp : bv 64) : reg_map :=
  <["PC" := RVal_Bits writeSuccess15d30NextPc]>
    (<["x2" := RVal_Bits (sp + BV 64 16)%bv]> regs).

Lemma writeSuccess15d30RegsLookupOther regs sp reg :
  reg <> "PC" ->
  reg <> "x2" ->
  writeSuccess15d30Regs regs sp !! reg = regs !! reg.
Proof.
  intros Hpc Hx10. unfold writeSuccess15d30Regs.
  rewrite lookup_insert_ne; last congruence.
  rewrite lookup_insert_ne; last congruence.
  reflexivity.
Qed.

Definition writeSuccess15d30Local (trace : isla_trace) (regs : reg_map) :
    seq_local_state := {|
  seq_trace := trace;
  seq_regs := regs;
  seq_pc_reg := "PC";
  seq_nb_state := false
|}.

Definition writeSuccess15d30Before (regs : reg_map)
    (global : seq_global_state) : IslaState :=
  (writeSuccess15d30Local a15d30 regs, global).

Definition writeSuccess15d30After (regs : reg_map) (global : seq_global_state)
    (sp : bv 64) : IslaState :=
  (writeSuccess15d30Local a15d34 (writeSuccess15d30Regs regs sp), global).

Definition writeSuccess15d30Observation (local : seq_local_state)
    (global : seq_global_state) : IslaMicroObservation := {|
  microLabels := [];
  microAfter := (local, global)
|}.

Lemma writeSuccess15d30NextPcExact :
  writeSuccess15d30NextPc = Z_to_bv 64 0x15d34.
Proof. unfold writeSuccess15d30NextPc. bv_solve. Qed.

Definition writeSuccess15d30PrefixObservations (regs : reg_map)
    (global : seq_global_state) (sp : bv 64) : list IslaMicroObservation :=
  [writeSuccess15d30Observation
     (writeSuccess15d30Local writeSuccess15d30Trace1 regs) global;
   writeSuccess15d30Observation
     (writeSuccess15d30Local writeSuccess15d30Trace2 regs) global;
   writeSuccess15d30Observation
     (writeSuccess15d30Local writeSuccess15d30Trace3 regs) global;
   writeSuccess15d30Observation
     (writeSuccess15d30Local writeSuccess15d30Trace4 regs) global;
   writeSuccess15d30Observation
     (writeSuccess15d30Local writeSuccess15d30Trace5 regs) global;
   writeSuccess15d30Observation
     (writeSuccess15d30Local (writeSuccess15d30Trace6 sp) regs) global;
   writeSuccess15d30Observation
     (writeSuccess15d30Local (writeSuccess15d30Trace7 sp) regs) global;
   writeSuccess15d30Observation
     (writeSuccess15d30Local (writeSuccess15d30Trace8 sp) regs) global;
   writeSuccess15d30Observation
     (writeSuccess15d30Local (writeSuccess15d30Trace9 sp)
       (<["x2" := RVal_Bits (sp + BV 64 16)%bv]> regs)) global;
   writeSuccess15d30Observation
     (writeSuccess15d30Local (writeSuccess15d30Trace10 sp)
       (writeSuccess15d30Regs regs sp)) global].

Definition writeSuccess15d30Observations (regs : reg_map)
    (global : seq_global_state) (sp : bv 64) : list IslaMicroObservation :=
  writeSuccess15d30PrefixObservations regs global sp ++
  [writeSuccess15d30Observation
     (writeSuccess15d30After regs global sp).1 global].

Lemma writeSuccess15d30TakeStep before observations done :
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

Lemma segment_15d30_mstatus (regs : reg_map) (global : seq_global_state)
    (sp : bv 64) oldX2 :
  regs !! "PC" = Some (RVal_Bits (Z_to_bv 64 0x15d30)) ->
  regs !! "x2" = Some (RVal_Bits sp) ->
  regs !! "x2" = Some oldX2 ->
  global.(seq_instrs) !! Z_to_bv 64 0x15d30 = Some a15d30 ->
  global.(seq_instrs) !! Z_to_bv 64 0x15d34 = Some a15d34 ->
  eval_a_exp regs writeSuccess15d30Mstatus = Some (Val_Bool true) ->
  IslaInstructionSegment (writeSuccess15d30Before regs global)
    (writeSuccess15d30Observations regs global sp)
    (writeSuccess15d30After regs global sp) /\
  (writeSuccess15d30After regs global sp).1.(seq_regs) =
    writeSuccess15d30Regs regs sp /\
  (writeSuccess15d30After regs global sp).2.(seq_mem) = global.(seq_mem) /\
  concat (map microLabels (writeSuccess15d30Observations regs global sp)) = [].
Proof.
  intros Hpc Hsp Hx10 Hcode Hnext Hmstatus.
  split; [|repeat split; reflexivity].
  unfold writeSuccess15d30Observations.
  eapply islaInstructionSegmentIntro with
    (done := (writeSuccess15d30Local tnil (writeSuccess15d30Regs regs sp), global))
    (labels := []) (spawned := []).
  - split; first reflexivity. exists (Z_to_bv 64 0x15d30), a15d30.
    cbn. rewrite Hpc Hcode. repeat split; reflexivity.
  - unfold writeSuccess15d30PrefixObservations.
    eapply IslaInstructionPrefixStep; first discriminate.
    { apply writeSuccessSeqSilent; first reflexivity.
      unfold writeSuccess15d30Before, writeSuccess15d30Local,
        writeSuccess15d30Trace1, writeSuccessTraceTail, a15d30. cbn.
      apply DeclareConstBitVecS' with (b := BV 64 0). }
    eapply IslaInstructionPrefixStep; first discriminate.
    { apply writeSuccessSeqAssume; first reflexivity.
      unfold writeSuccess15d30Trace1, writeSuccessTraceTail, a15d30. cbn.
      eapply AssumeS. exact Hmstatus. }
    eapply IslaInstructionPrefixStep; first discriminate.
    { apply writeSuccessSeqSilent; first reflexivity.
      unfold writeSuccess15d30Trace2, writeSuccess15d30Trace1,
        writeSuccessTraceTail, a15d30. cbn.
      apply DeclareConstBitVecS' with (b := Z_to_bv 64 0x15d30). }
    eapply IslaInstructionPrefixStep; first discriminate.
    { eapply writeSuccessSeqReadReg with
        (root := RVal_Bits (Z_to_bv 64 0x15d30))
        (value := RVal_Bits (Z_to_bv 64 0x15d30)).
      - reflexivity.
      - unfold writeSuccess15d30Trace3, writeSuccess15d30Trace2,
          writeSuccess15d30Trace1, writeSuccessTraceTail, a15d30. cbn.
        constructor.
      - exact Hpc.
      - reflexivity.
      - reflexivity. }
    eapply IslaInstructionPrefixStep; first discriminate.
    { apply writeSuccessSeqSilent; first reflexivity.
      unfold writeSuccess15d30Trace5, writeSuccess15d30Trace4, writeSuccess15d30Trace3,
        writeSuccess15d30Trace2, writeSuccess15d30Trace1,
        writeSuccess15d30NextPc, writeSuccessTraceTail, a15d30. cbn.
      eapply DefineConstS with
        (v := Val_Bits (Z_to_bv 64 0x15d30 + BV 64 4)%bv).
      reflexivity. }
    eapply IslaInstructionPrefixStep; first discriminate.
    { apply writeSuccessSeqSilent; first reflexivity.
      unfold writeSuccess15d30Trace5, writeSuccess15d30Trace4,
        writeSuccess15d30Trace3, writeSuccess15d30Trace2,
        writeSuccess15d30Trace1, writeSuccessTraceTail, a15d30. cbn.
      apply DeclareConstBitVecS' with (b := sp). }
    eapply IslaInstructionPrefixStep; first discriminate.
    { eapply writeSuccessSeqReadReg with
        (root := RVal_Bits sp) (value := RVal_Bits sp).
      - reflexivity.
      - unfold writeSuccess15d30Trace6, writeSuccess15d30Trace5,
          writeSuccess15d30Trace4, writeSuccess15d30Trace3,
          writeSuccess15d30Trace2, writeSuccess15d30Trace1,
          writeSuccessTraceTail, a15d30. cbn. constructor.
      - exact Hsp.
      - reflexivity.
      - reflexivity. }
    eapply IslaInstructionPrefixStep; first discriminate.
    { apply writeSuccessSeqSilent; first reflexivity.
      unfold writeSuccess15d30Trace7, writeSuccess15d30Trace6,
        writeSuccess15d30Trace5, writeSuccess15d30Trace4,
        writeSuccess15d30Trace3, writeSuccess15d30Trace2,
        writeSuccess15d30Trace1, writeSuccessTraceTail, a15d30. cbn.
      eapply DefineConstS with (v := Val_Bits (sp + BV 64 16)%bv).
      reflexivity. }
    eapply IslaInstructionPrefixStep; first discriminate.
    { eapply writeSuccessSeqWriteReg with (root := oldX2)
        (value := RVal_Bits (sp + BV 64 16)%bv)
        (updated := RVal_Bits (sp + BV 64 16)%bv).
      - reflexivity.
      - unfold writeSuccess15d30Trace8, writeSuccess15d30Trace7,
          writeSuccess15d30Trace6, writeSuccess15d30Trace5,
          writeSuccess15d30Trace4, writeSuccess15d30Trace3,
          writeSuccess15d30Trace2, writeSuccess15d30Trace1,
          writeSuccessTraceTail, a15d30. cbn. constructor.
      - exact Hx10.
      - reflexivity.
      - reflexivity. }
    eapply IslaInstructionPrefixStep; first discriminate.
    { eapply writeSuccessSeqWriteReg with
        (root := RVal_Bits (Z_to_bv 64 0x15d30))
        (value := RVal_Bits writeSuccess15d30NextPc)
        (updated := RVal_Bits writeSuccess15d30NextPc).
      - reflexivity.
      - unfold writeSuccess15d30Trace9, writeSuccess15d30Trace8,
          writeSuccess15d30Trace7, writeSuccess15d30Trace6,
          writeSuccess15d30Trace5, writeSuccess15d30Trace4,
          writeSuccess15d30Trace3, writeSuccess15d30Trace2,
          writeSuccess15d30Trace1, writeSuccessTraceTail, a15d30. cbn.
        constructor.
      - rewrite lookup_insert_ne; last done. exact Hpc.
      - reflexivity.
      - reflexivity. }
    apply IslaInstructionPrefixRefl.
  - reflexivity.
  - apply writeSuccessSeqDoneTabled with (next := a15d34) (trace := a15d34).
    + reflexivity.
    + reflexivity.
    + constructor.
    + exists (Z_to_bv 64 0x15d34).
      unfold writeSuccess15d30Regs. rewrite lookup_insert.
      rewrite writeSuccess15d30NextPcExact Hnext.
      repeat split; reflexivity.
  - left. split; first reflexivity. exists (Z_to_bv 64 0x15d34), a15d34.
    cbn. unfold writeSuccess15d30Regs. rewrite lookup_insert.
    rewrite writeSuccess15d30NextPcExact Hnext.
    repeat split; reflexivity.
Qed.

Lemma segment_15d30 (regs : reg_map) (global : seq_global_state)
    (sp : bv 64) oldX2 :
  regs !! "PC" = Some (RVal_Bits (Z_to_bv 64 0x15d30)) ->
  regs !! "x2" = Some (RVal_Bits sp) ->
  regs !! "x2" = Some oldX2 ->
  global.(seq_instrs) !! Z_to_bv 64 0x15d30 = Some a15d30 ->
  global.(seq_instrs) !! Z_to_bv 64 0x15d34 = Some a15d34 ->
  eval_a_exp regs writeSuccess15d30Mstatus = Some (Val_Bool true) ->
  IslaInstructionSegment (writeSuccess15d30Before regs global)
    (writeSuccess15d30Observations regs global sp)
    (writeSuccess15d30After regs global sp) /\
  (writeSuccess15d30After regs global sp).1.(seq_regs) =
    writeSuccess15d30Regs regs sp /\
  (writeSuccess15d30After regs global sp).2.(seq_mem) = global.(seq_mem) /\
  concat (map microLabels (writeSuccess15d30Observations regs global sp)) = [].
Proof.
  intros Hpc Hsp Hx10 Hcode Hnext Hmstatus.
  eapply segment_15d30_mstatus; eauto.
Qed.

Print Assumptions writeSuccess15d30NextPcExact.
Print Assumptions segment_15d30_mstatus.
Print Assumptions segment_15d30.
Print Assumptions writeSuccess15d30RegsLookupOther.
