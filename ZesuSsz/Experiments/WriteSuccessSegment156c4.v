From Coq Require Import Eqdep_dec Lists.List ZArith.ZArith.
Require Import isla.riscv64.riscv64.
Require Import IslaTraces.write_success_93.a156c4.
Require Import IslaTraces.write_success_93.a156c8.
Require Import ZesuSsz.Contracts.InstructionBoundary.
Require Import ZesuSsz.Experiments.WriteSuccessSegmentAutomation.
Require Import ZesuSsz.Experiments.WriteSuccessCoverageAutomation.

Import ListNotations.
Open Scope Z_scope.

Definition writeSuccessTraceTail (trace : isla_trace) : isla_trace :=
  match trace with tcons _ rest => rest | _ => tnil end.

Definition writeSuccess156c4Mstatus : a_exp :=
  AExp_Binop Eq
    (AExp_Manyop (Bvmanyarith Bvand)
      [AExp_Val (AVal_Var "mstatus" [Field "bits"]) Mk_annot;
       AExp_Val (AVal_Bits (BV 64 0x20000)) Mk_annot] Mk_annot)
    (AExp_Val (AVal_Bits (BV 64 0)) Mk_annot) Mk_annot.

Definition writeSuccess156c4Trace1 :=
  subst_trace (Val_Bits (BV 64 0)) 2 (writeSuccessTraceTail a156c4).
Definition writeSuccess156c4Trace2 := writeSuccessTraceTail writeSuccess156c4Trace1.
Definition writeSuccess156c4Trace3 :=
  subst_trace (Val_Bits (Z_to_bv 64 0x156c4)) 3
    (writeSuccessTraceTail writeSuccess156c4Trace2).
Definition writeSuccess156c4Trace4 := writeSuccessTraceTail writeSuccess156c4Trace3.
Definition writeSuccess156c4NextPc : bv 64 :=
  (Z_to_bv 64 0x156c4 + BV 64 4)%bv.
Definition writeSuccess156c4Trace5 :=
  subst_trace (Val_Bits writeSuccess156c4NextPc) 4
    (writeSuccessTraceTail writeSuccess156c4Trace4).
Definition writeSuccess156c4Trace6 (sp : bv 64) :=
  subst_trace (Val_Bits sp) 5 (writeSuccessTraceTail writeSuccess156c4Trace5).
Definition writeSuccess156c4Trace7 (sp : bv 64) :=
  writeSuccessTraceTail (writeSuccess156c4Trace6 sp).
Definition writeSuccess156c4Trace8 (sp : bv 64) :=
  subst_trace (Val_Bits (sp + BV 64 0)%bv) 6
    (writeSuccessTraceTail (writeSuccess156c4Trace7 sp)).
Definition writeSuccess156c4Trace9 (sp : bv 64) :=
  writeSuccessTraceTail (writeSuccess156c4Trace8 sp).
Definition writeSuccess156c4Trace10 (sp : bv 64) :=
  writeSuccessTraceTail (writeSuccess156c4Trace9 sp).

Definition writeSuccess156c4Regs (regs : reg_map) (sp : bv 64) : reg_map :=
  <["PC" := RVal_Bits writeSuccess156c4NextPc]>
    (<["x10" := RVal_Bits (sp + BV 64 0)%bv]> regs).

Lemma writeSuccess156c4RegsLookupOther regs sp reg :
  reg <> "PC" ->
  reg <> "x10" ->
  writeSuccess156c4Regs regs sp !! reg = regs !! reg.
Proof.
  intros Hpc Hx10. unfold writeSuccess156c4Regs.
  rewrite lookup_insert_ne; last congruence.
  rewrite lookup_insert_ne; last congruence.
  reflexivity.
Qed.

Definition writeSuccess156c4Local (trace : isla_trace) (regs : reg_map) :
    seq_local_state := {|
  seq_trace := trace;
  seq_regs := regs;
  seq_pc_reg := "PC";
  seq_nb_state := false
|}.

Definition writeSuccess156c4Before (regs : reg_map)
    (global : seq_global_state) : IslaState :=
  (writeSuccess156c4Local a156c4 regs, global).

Definition writeSuccess156c4After (regs : reg_map) (global : seq_global_state)
    (sp : bv 64) : IslaState :=
  (writeSuccess156c4Local a156c8 (writeSuccess156c4Regs regs sp), global).

Definition writeSuccess156c4Observation (local : seq_local_state)
    (global : seq_global_state) : IslaMicroObservation := {|
  microLabels := [];
  microAfter := (local, global)
|}.

Lemma writeSuccess156c4NextPcExact :
  writeSuccess156c4NextPc = Z_to_bv 64 0x156c8.
Proof. unfold writeSuccess156c4NextPc. bv_solve. Qed.

Definition writeSuccess156c4PrefixObservations (regs : reg_map)
    (global : seq_global_state) (sp : bv 64) : list IslaMicroObservation :=
  [writeSuccess156c4Observation
     (writeSuccess156c4Local writeSuccess156c4Trace1 regs) global;
   writeSuccess156c4Observation
     (writeSuccess156c4Local writeSuccess156c4Trace2 regs) global;
   writeSuccess156c4Observation
     (writeSuccess156c4Local writeSuccess156c4Trace3 regs) global;
   writeSuccess156c4Observation
     (writeSuccess156c4Local writeSuccess156c4Trace4 regs) global;
   writeSuccess156c4Observation
     (writeSuccess156c4Local writeSuccess156c4Trace5 regs) global;
   writeSuccess156c4Observation
     (writeSuccess156c4Local (writeSuccess156c4Trace6 sp) regs) global;
   writeSuccess156c4Observation
     (writeSuccess156c4Local (writeSuccess156c4Trace7 sp) regs) global;
   writeSuccess156c4Observation
     (writeSuccess156c4Local (writeSuccess156c4Trace8 sp) regs) global;
   writeSuccess156c4Observation
     (writeSuccess156c4Local (writeSuccess156c4Trace9 sp)
       (<["x10" := RVal_Bits (sp + BV 64 0)%bv]> regs)) global;
   writeSuccess156c4Observation
     (writeSuccess156c4Local (writeSuccess156c4Trace10 sp)
       (writeSuccess156c4Regs regs sp)) global].

Definition writeSuccess156c4Observations (regs : reg_map)
    (global : seq_global_state) (sp : bv 64) : list IslaMicroObservation :=
  writeSuccess156c4PrefixObservations regs global sp ++
  [writeSuccess156c4Observation
     (writeSuccess156c4After regs global sp).1 global].

Lemma writeSuccess156c4TakeStep before observations done :
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

Lemma segment_156c4_mstatus (regs : reg_map) (global : seq_global_state)
    (sp : bv 64) oldX10 :
  regs !! "PC" = Some (RVal_Bits (Z_to_bv 64 0x156c4)) ->
  regs !! "x18" = Some (RVal_Bits sp) ->
  regs !! "x10" = Some oldX10 ->
  global.(seq_instrs) !! Z_to_bv 64 0x156c4 = Some a156c4 ->
  global.(seq_instrs) !! Z_to_bv 64 0x156c8 = Some a156c8 ->
  eval_a_exp regs writeSuccess156c4Mstatus = Some (Val_Bool true) ->
  IslaInstructionSegment (writeSuccess156c4Before regs global)
    (writeSuccess156c4Observations regs global sp)
    (writeSuccess156c4After regs global sp) /\
  (writeSuccess156c4After regs global sp).1.(seq_regs) =
    writeSuccess156c4Regs regs sp /\
  (writeSuccess156c4After regs global sp).2.(seq_mem) = global.(seq_mem) /\
  concat (map microLabels (writeSuccess156c4Observations regs global sp)) = [].
Proof.
  intros Hpc Hsp Hx10 Hcode Hnext Hmstatus.
  split; [|repeat split; reflexivity].
  unfold writeSuccess156c4Observations.
  eapply islaInstructionSegmentIntro with
    (done := (writeSuccess156c4Local tnil (writeSuccess156c4Regs regs sp), global))
    (labels := []) (spawned := []).
  - split; first reflexivity. exists (Z_to_bv 64 0x156c4), a156c4.
    cbn. rewrite Hpc Hcode. repeat split; reflexivity.
  - unfold writeSuccess156c4PrefixObservations.
    eapply IslaInstructionPrefixStep; first discriminate.
    { apply writeSuccessSeqSilent; first reflexivity.
      unfold writeSuccess156c4Before, writeSuccess156c4Local,
        writeSuccess156c4Trace1, writeSuccessTraceTail, a156c4. cbn.
      apply DeclareConstBitVecS' with (b := BV 64 0). }
    eapply IslaInstructionPrefixStep; first discriminate.
    { apply writeSuccessSeqAssume; first reflexivity.
      unfold writeSuccess156c4Trace1, writeSuccessTraceTail, a156c4. cbn.
      eapply AssumeS. exact Hmstatus. }
    eapply IslaInstructionPrefixStep; first discriminate.
    { apply writeSuccessSeqSilent; first reflexivity.
      unfold writeSuccess156c4Trace2, writeSuccess156c4Trace1,
        writeSuccessTraceTail, a156c4. cbn.
      apply DeclareConstBitVecS' with (b := Z_to_bv 64 0x156c4). }
    eapply IslaInstructionPrefixStep; first discriminate.
    { eapply writeSuccessSeqReadReg with
        (root := RVal_Bits (Z_to_bv 64 0x156c4))
        (value := RVal_Bits (Z_to_bv 64 0x156c4)).
      - reflexivity.
      - unfold writeSuccess156c4Trace3, writeSuccess156c4Trace2,
          writeSuccess156c4Trace1, writeSuccessTraceTail, a156c4. cbn.
        constructor.
      - exact Hpc.
      - reflexivity.
      - reflexivity. }
    eapply IslaInstructionPrefixStep; first discriminate.
    { apply writeSuccessSeqSilent; first reflexivity.
      unfold writeSuccess156c4Trace5, writeSuccess156c4Trace4, writeSuccess156c4Trace3,
        writeSuccess156c4Trace2, writeSuccess156c4Trace1,
        writeSuccess156c4NextPc, writeSuccessTraceTail, a156c4. cbn.
      eapply DefineConstS with
        (v := Val_Bits (Z_to_bv 64 0x156c4 + BV 64 4)%bv).
      reflexivity. }
    eapply IslaInstructionPrefixStep; first discriminate.
    { apply writeSuccessSeqSilent; first reflexivity.
      unfold writeSuccess156c4Trace5, writeSuccess156c4Trace4,
        writeSuccess156c4Trace3, writeSuccess156c4Trace2,
        writeSuccess156c4Trace1, writeSuccessTraceTail, a156c4. cbn.
      apply DeclareConstBitVecS' with (b := sp). }
    eapply IslaInstructionPrefixStep; first discriminate.
    { eapply writeSuccessSeqReadReg with
        (root := RVal_Bits sp) (value := RVal_Bits sp).
      - reflexivity.
      - unfold writeSuccess156c4Trace6, writeSuccess156c4Trace5,
          writeSuccess156c4Trace4, writeSuccess156c4Trace3,
          writeSuccess156c4Trace2, writeSuccess156c4Trace1,
          writeSuccessTraceTail, a156c4. cbn. constructor.
      - exact Hsp.
      - reflexivity.
      - reflexivity. }
    eapply IslaInstructionPrefixStep; first discriminate.
    { apply writeSuccessSeqSilent; first reflexivity.
      unfold writeSuccess156c4Trace7, writeSuccess156c4Trace6,
        writeSuccess156c4Trace5, writeSuccess156c4Trace4,
        writeSuccess156c4Trace3, writeSuccess156c4Trace2,
        writeSuccess156c4Trace1, writeSuccessTraceTail, a156c4. cbn.
      eapply DefineConstS with (v := Val_Bits (sp + BV 64 0)%bv).
      reflexivity. }
    eapply IslaInstructionPrefixStep; first discriminate.
    { eapply writeSuccessSeqWriteReg with (root := oldX10)
        (value := RVal_Bits (sp + BV 64 0)%bv)
        (updated := RVal_Bits (sp + BV 64 0)%bv).
      - reflexivity.
      - unfold writeSuccess156c4Trace8, writeSuccess156c4Trace7,
          writeSuccess156c4Trace6, writeSuccess156c4Trace5,
          writeSuccess156c4Trace4, writeSuccess156c4Trace3,
          writeSuccess156c4Trace2, writeSuccess156c4Trace1,
          writeSuccessTraceTail, a156c4. cbn. constructor.
      - exact Hx10.
      - reflexivity.
      - reflexivity. }
    eapply IslaInstructionPrefixStep; first discriminate.
    { eapply writeSuccessSeqWriteReg with
        (root := RVal_Bits (Z_to_bv 64 0x156c4))
        (value := RVal_Bits writeSuccess156c4NextPc)
        (updated := RVal_Bits writeSuccess156c4NextPc).
      - reflexivity.
      - unfold writeSuccess156c4Trace9, writeSuccess156c4Trace8,
          writeSuccess156c4Trace7, writeSuccess156c4Trace6,
          writeSuccess156c4Trace5, writeSuccess156c4Trace4,
          writeSuccess156c4Trace3, writeSuccess156c4Trace2,
          writeSuccess156c4Trace1, writeSuccessTraceTail, a156c4. cbn.
        constructor.
      - rewrite lookup_insert_ne; last done. exact Hpc.
      - reflexivity.
      - reflexivity. }
    apply IslaInstructionPrefixRefl.
  - reflexivity.
  - apply writeSuccessSeqDoneTabled with (next := a156c8) (trace := a156c8).
    + reflexivity.
    + reflexivity.
    + constructor.
    + exists (Z_to_bv 64 0x156c8).
      unfold writeSuccess156c4Regs. rewrite lookup_insert.
      rewrite writeSuccess156c4NextPcExact Hnext.
      repeat split; reflexivity.
  - left. split; first reflexivity. exists (Z_to_bv 64 0x156c8), a156c8.
    cbn. unfold writeSuccess156c4Regs. rewrite lookup_insert.
    rewrite writeSuccess156c4NextPcExact Hnext.
    repeat split; reflexivity.
Qed.

Lemma segment_156c4 (regs : reg_map) (global : seq_global_state)
    (sp : bv 64) oldX10 :
  regs !! "PC" = Some (RVal_Bits (Z_to_bv 64 0x156c4)) ->
  regs !! "x18" = Some (RVal_Bits sp) ->
  regs !! "x10" = Some oldX10 ->
  global.(seq_instrs) !! Z_to_bv 64 0x156c4 = Some a156c4 ->
  global.(seq_instrs) !! Z_to_bv 64 0x156c8 = Some a156c8 ->
  eval_a_exp regs writeSuccess156c4Mstatus = Some (Val_Bool true) ->
  IslaInstructionSegment (writeSuccess156c4Before regs global)
    (writeSuccess156c4Observations regs global sp)
    (writeSuccess156c4After regs global sp) /\
  (writeSuccess156c4After regs global sp).1.(seq_regs) =
    writeSuccess156c4Regs regs sp /\
  (writeSuccess156c4After regs global sp).2.(seq_mem) = global.(seq_mem) /\
  concat (map microLabels (writeSuccess156c4Observations regs global sp)) = [].
Proof.
  intros Hpc Hsp Hx10 Hcode Hnext Hmstatus.
  eapply segment_156c4_mstatus; eauto.
Qed.

Print Assumptions writeSuccess156c4NextPcExact.
Print Assumptions segment_156c4_mstatus.
Print Assumptions segment_156c4.
Print Assumptions writeSuccess156c4RegsLookupOther.
