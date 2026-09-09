From Coq Require Import Eqdep_dec Lists.List ZArith.ZArith.
Require Import isla.riscv64.riscv64.
Require Import IslaTraces.write_success_95.a156e0.
Require Import IslaTraces.write_success_95.a156e4.
Require Import ZesuSsz.Contracts.InstructionBoundary.
Require Import ZesuSsz.Experiments.WriteSuccessSegmentAutomation.
Require Import ZesuSsz.Experiments.WriteSuccessCoverageAutomation.

Import ListNotations.
Open Scope Z_scope.

Definition writeSuccessTraceTail (trace : isla_trace) : isla_trace :=
  match trace with tcons _ rest => rest | _ => tnil end.

Definition writeSuccess156e0Mstatus : a_exp :=
  AExp_Binop Eq
    (AExp_Manyop (Bvmanyarith Bvand)
      [AExp_Val (AVal_Var "mstatus" [Field "bits"]) Mk_annot;
       AExp_Val (AVal_Bits (BV 64 0x20000)) Mk_annot] Mk_annot)
    (AExp_Val (AVal_Bits (BV 64 0)) Mk_annot) Mk_annot.

Definition writeSuccess156e0Trace1 :=
  subst_trace (Val_Bits (BV 64 0)) 2 (writeSuccessTraceTail a156e0).
Definition writeSuccess156e0Trace2 := writeSuccessTraceTail writeSuccess156e0Trace1.
Definition writeSuccess156e0Trace3 :=
  subst_trace (Val_Bits (Z_to_bv 64 0x156e0)) 3
    (writeSuccessTraceTail writeSuccess156e0Trace2).
Definition writeSuccess156e0Trace4 := writeSuccessTraceTail writeSuccess156e0Trace3.
Definition writeSuccess156e0NextPc : bv 64 :=
  (Z_to_bv 64 0x156e0 + BV 64 4)%bv.
Definition writeSuccess156e0Trace5 :=
  subst_trace (Val_Bits writeSuccess156e0NextPc) 4
    (writeSuccessTraceTail writeSuccess156e0Trace4).
Definition writeSuccess156e0Trace6 (sp : bv 64) :=
  subst_trace (Val_Bits sp) 5 (writeSuccessTraceTail writeSuccess156e0Trace5).
Definition writeSuccess156e0Trace7 (sp : bv 64) :=
  writeSuccessTraceTail (writeSuccess156e0Trace6 sp).
Definition writeSuccess156e0Trace8 (sp : bv 64) :=
  subst_trace (Val_Bits (sp + BV 64 18446744073709551615)%bv) 6
    (writeSuccessTraceTail (writeSuccess156e0Trace7 sp)).
Definition writeSuccess156e0Trace9 (sp : bv 64) :=
  writeSuccessTraceTail (writeSuccess156e0Trace8 sp).
Definition writeSuccess156e0Trace10 (sp : bv 64) :=
  writeSuccessTraceTail (writeSuccess156e0Trace9 sp).

Definition writeSuccess156e0Regs (regs : reg_map) (sp : bv 64) : reg_map :=
  <["PC" := RVal_Bits writeSuccess156e0NextPc]>
    (<["x9" := RVal_Bits (sp + BV 64 18446744073709551615)%bv]> regs).

Lemma writeSuccess156e0RegsLookupOther regs sp reg :
  reg <> "PC" ->
  reg <> "x9" ->
  writeSuccess156e0Regs regs sp !! reg = regs !! reg.
Proof.
  intros Hpc Hx10. unfold writeSuccess156e0Regs.
  rewrite lookup_insert_ne; last congruence.
  rewrite lookup_insert_ne; last congruence.
  reflexivity.
Qed.

Definition writeSuccess156e0Local (trace : isla_trace) (regs : reg_map) :
    seq_local_state := {|
  seq_trace := trace;
  seq_regs := regs;
  seq_pc_reg := "PC";
  seq_nb_state := false
|}.

Definition writeSuccess156e0Before (regs : reg_map)
    (global : seq_global_state) : IslaState :=
  (writeSuccess156e0Local a156e0 regs, global).

Definition writeSuccess156e0After (regs : reg_map) (global : seq_global_state)
    (sp : bv 64) : IslaState :=
  (writeSuccess156e0Local a156e4 (writeSuccess156e0Regs regs sp), global).

Definition writeSuccess156e0Observation (local : seq_local_state)
    (global : seq_global_state) : IslaMicroObservation := {|
  microLabels := [];
  microAfter := (local, global)
|}.

Lemma writeSuccess156e0NextPcExact :
  writeSuccess156e0NextPc = Z_to_bv 64 0x156e4.
Proof. unfold writeSuccess156e0NextPc. bv_solve. Qed.

Definition writeSuccess156e0PrefixObservations (regs : reg_map)
    (global : seq_global_state) (sp : bv 64) : list IslaMicroObservation :=
  [writeSuccess156e0Observation
     (writeSuccess156e0Local writeSuccess156e0Trace1 regs) global;
   writeSuccess156e0Observation
     (writeSuccess156e0Local writeSuccess156e0Trace2 regs) global;
   writeSuccess156e0Observation
     (writeSuccess156e0Local writeSuccess156e0Trace3 regs) global;
   writeSuccess156e0Observation
     (writeSuccess156e0Local writeSuccess156e0Trace4 regs) global;
   writeSuccess156e0Observation
     (writeSuccess156e0Local writeSuccess156e0Trace5 regs) global;
   writeSuccess156e0Observation
     (writeSuccess156e0Local (writeSuccess156e0Trace6 sp) regs) global;
   writeSuccess156e0Observation
     (writeSuccess156e0Local (writeSuccess156e0Trace7 sp) regs) global;
   writeSuccess156e0Observation
     (writeSuccess156e0Local (writeSuccess156e0Trace8 sp) regs) global;
   writeSuccess156e0Observation
     (writeSuccess156e0Local (writeSuccess156e0Trace9 sp)
       (<["x9" := RVal_Bits (sp + BV 64 18446744073709551615)%bv]> regs)) global;
   writeSuccess156e0Observation
     (writeSuccess156e0Local (writeSuccess156e0Trace10 sp)
       (writeSuccess156e0Regs regs sp)) global].

Definition writeSuccess156e0Observations (regs : reg_map)
    (global : seq_global_state) (sp : bv 64) : list IslaMicroObservation :=
  writeSuccess156e0PrefixObservations regs global sp ++
  [writeSuccess156e0Observation
     (writeSuccess156e0After regs global sp).1 global].

Lemma writeSuccess156e0TakeStep before observations done :
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

Lemma segment_156e0_mstatus (regs : reg_map) (global : seq_global_state)
    (sp : bv 64) oldX9 :
  regs !! "PC" = Some (RVal_Bits (Z_to_bv 64 0x156e0)) ->
  regs !! "x9" = Some (RVal_Bits sp) ->
  regs !! "x9" = Some oldX9 ->
  global.(seq_instrs) !! Z_to_bv 64 0x156e0 = Some a156e0 ->
  global.(seq_instrs) !! Z_to_bv 64 0x156e4 = Some a156e4 ->
  eval_a_exp regs writeSuccess156e0Mstatus = Some (Val_Bool true) ->
  IslaInstructionSegment (writeSuccess156e0Before regs global)
    (writeSuccess156e0Observations regs global sp)
    (writeSuccess156e0After regs global sp) /\
  (writeSuccess156e0After regs global sp).1.(seq_regs) =
    writeSuccess156e0Regs regs sp /\
  (writeSuccess156e0After regs global sp).2.(seq_mem) = global.(seq_mem) /\
  concat (map microLabels (writeSuccess156e0Observations regs global sp)) = [].
Proof.
  intros Hpc Hsp Hx10 Hcode Hnext Hmstatus.
  split; [|repeat split; reflexivity].
  unfold writeSuccess156e0Observations.
  eapply islaInstructionSegmentIntro with
    (done := (writeSuccess156e0Local tnil (writeSuccess156e0Regs regs sp), global))
    (labels := []) (spawned := []).
  - split; first reflexivity. exists (Z_to_bv 64 0x156e0), a156e0.
    cbn. rewrite Hpc Hcode. repeat split; reflexivity.
  - unfold writeSuccess156e0PrefixObservations.
    eapply IslaInstructionPrefixStep; first discriminate.
    { apply writeSuccessSeqSilent; first reflexivity.
      unfold writeSuccess156e0Before, writeSuccess156e0Local,
        writeSuccess156e0Trace1, writeSuccessTraceTail, a156e0. cbn.
      apply DeclareConstBitVecS' with (b := BV 64 0). }
    eapply IslaInstructionPrefixStep; first discriminate.
    { apply writeSuccessSeqAssume; first reflexivity.
      unfold writeSuccess156e0Trace1, writeSuccessTraceTail, a156e0. cbn.
      eapply AssumeS. exact Hmstatus. }
    eapply IslaInstructionPrefixStep; first discriminate.
    { apply writeSuccessSeqSilent; first reflexivity.
      unfold writeSuccess156e0Trace2, writeSuccess156e0Trace1,
        writeSuccessTraceTail, a156e0. cbn.
      apply DeclareConstBitVecS' with (b := Z_to_bv 64 0x156e0). }
    eapply IslaInstructionPrefixStep; first discriminate.
    { eapply writeSuccessSeqReadReg with
        (root := RVal_Bits (Z_to_bv 64 0x156e0))
        (value := RVal_Bits (Z_to_bv 64 0x156e0)).
      - reflexivity.
      - unfold writeSuccess156e0Trace3, writeSuccess156e0Trace2,
          writeSuccess156e0Trace1, writeSuccessTraceTail, a156e0. cbn.
        constructor.
      - exact Hpc.
      - reflexivity.
      - reflexivity. }
    eapply IslaInstructionPrefixStep; first discriminate.
    { apply writeSuccessSeqSilent; first reflexivity.
      unfold writeSuccess156e0Trace5, writeSuccess156e0Trace4, writeSuccess156e0Trace3,
        writeSuccess156e0Trace2, writeSuccess156e0Trace1,
        writeSuccess156e0NextPc, writeSuccessTraceTail, a156e0. cbn.
      eapply DefineConstS with
        (v := Val_Bits (Z_to_bv 64 0x156e0 + BV 64 4)%bv).
      reflexivity. }
    eapply IslaInstructionPrefixStep; first discriminate.
    { apply writeSuccessSeqSilent; first reflexivity.
      unfold writeSuccess156e0Trace5, writeSuccess156e0Trace4,
        writeSuccess156e0Trace3, writeSuccess156e0Trace2,
        writeSuccess156e0Trace1, writeSuccessTraceTail, a156e0. cbn.
      apply DeclareConstBitVecS' with (b := sp). }
    eapply IslaInstructionPrefixStep; first discriminate.
    { eapply writeSuccessSeqReadReg with
        (root := RVal_Bits sp) (value := RVal_Bits sp).
      - reflexivity.
      - unfold writeSuccess156e0Trace6, writeSuccess156e0Trace5,
          writeSuccess156e0Trace4, writeSuccess156e0Trace3,
          writeSuccess156e0Trace2, writeSuccess156e0Trace1,
          writeSuccessTraceTail, a156e0. cbn. constructor.
      - exact Hsp.
      - reflexivity.
      - reflexivity. }
    eapply IslaInstructionPrefixStep; first discriminate.
    { apply writeSuccessSeqSilent; first reflexivity.
      unfold writeSuccess156e0Trace7, writeSuccess156e0Trace6,
        writeSuccess156e0Trace5, writeSuccess156e0Trace4,
        writeSuccess156e0Trace3, writeSuccess156e0Trace2,
        writeSuccess156e0Trace1, writeSuccessTraceTail, a156e0. cbn.
      eapply DefineConstS with (v := Val_Bits (sp + BV 64 18446744073709551615)%bv).
      reflexivity. }
    eapply IslaInstructionPrefixStep; first discriminate.
    { eapply writeSuccessSeqWriteReg with (root := oldX9)
        (value := RVal_Bits (sp + BV 64 18446744073709551615)%bv)
        (updated := RVal_Bits (sp + BV 64 18446744073709551615)%bv).
      - reflexivity.
      - unfold writeSuccess156e0Trace8, writeSuccess156e0Trace7,
          writeSuccess156e0Trace6, writeSuccess156e0Trace5,
          writeSuccess156e0Trace4, writeSuccess156e0Trace3,
          writeSuccess156e0Trace2, writeSuccess156e0Trace1,
          writeSuccessTraceTail, a156e0. cbn. constructor.
      - exact Hx10.
      - reflexivity.
      - reflexivity. }
    eapply IslaInstructionPrefixStep; first discriminate.
    { eapply writeSuccessSeqWriteReg with
        (root := RVal_Bits (Z_to_bv 64 0x156e0))
        (value := RVal_Bits writeSuccess156e0NextPc)
        (updated := RVal_Bits writeSuccess156e0NextPc).
      - reflexivity.
      - unfold writeSuccess156e0Trace9, writeSuccess156e0Trace8,
          writeSuccess156e0Trace7, writeSuccess156e0Trace6,
          writeSuccess156e0Trace5, writeSuccess156e0Trace4,
          writeSuccess156e0Trace3, writeSuccess156e0Trace2,
          writeSuccess156e0Trace1, writeSuccessTraceTail, a156e0. cbn.
        constructor.
      - rewrite lookup_insert_ne; last done. exact Hpc.
      - reflexivity.
      - reflexivity. }
    apply IslaInstructionPrefixRefl.
  - reflexivity.
  - apply writeSuccessSeqDoneTabled with (next := a156e4) (trace := a156e4).
    + reflexivity.
    + reflexivity.
    + constructor.
    + exists (Z_to_bv 64 0x156e4).
      unfold writeSuccess156e0Regs. rewrite lookup_insert.
      rewrite writeSuccess156e0NextPcExact Hnext.
      repeat split; reflexivity.
  - left. split; first reflexivity. exists (Z_to_bv 64 0x156e4), a156e4.
    cbn. unfold writeSuccess156e0Regs. rewrite lookup_insert.
    rewrite writeSuccess156e0NextPcExact Hnext.
    repeat split; reflexivity.
Qed.

Lemma segment_156e0 (regs : reg_map) (global : seq_global_state)
    (sp : bv 64) oldX9 :
  regs !! "PC" = Some (RVal_Bits (Z_to_bv 64 0x156e0)) ->
  regs !! "x9" = Some (RVal_Bits sp) ->
  regs !! "x9" = Some oldX9 ->
  global.(seq_instrs) !! Z_to_bv 64 0x156e0 = Some a156e0 ->
  global.(seq_instrs) !! Z_to_bv 64 0x156e4 = Some a156e4 ->
  eval_a_exp regs writeSuccess156e0Mstatus = Some (Val_Bool true) ->
  IslaInstructionSegment (writeSuccess156e0Before regs global)
    (writeSuccess156e0Observations regs global sp)
    (writeSuccess156e0After regs global sp) /\
  (writeSuccess156e0After regs global sp).1.(seq_regs) =
    writeSuccess156e0Regs regs sp /\
  (writeSuccess156e0After regs global sp).2.(seq_mem) = global.(seq_mem) /\
  concat (map microLabels (writeSuccess156e0Observations regs global sp)) = [].
Proof.
  intros Hpc Hsp Hx10 Hcode Hnext Hmstatus.
  eapply segment_156e0_mstatus; eauto.
Qed.

Print Assumptions writeSuccess156e0NextPcExact.
Print Assumptions segment_156e0_mstatus.
Print Assumptions segment_156e0.
Print Assumptions writeSuccess156e0RegsLookupOther.
