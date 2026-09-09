From Coq Require Import Eqdep_dec Lists.List ZArith.ZArith.
Require Import isla.riscv64.riscv64.
Require Import IslaTraces.write_success_90.a15694.
Require Import IslaTraces.write_success_90.a15698.
Require Import ZesuSsz.Contracts.InstructionBoundary.
Require Import ZesuSsz.Experiments.WriteSuccessSegmentAutomation.
Require Import ZesuSsz.Experiments.WriteSuccessCoverageAutomation.

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

Lemma segment_15694_mstatus (regs : reg_map) (global : seq_global_state)
    (sp : bv 64) oldX10 :
  regs !! "PC" = Some (RVal_Bits (Z_to_bv 64 0x15694)) ->
  regs !! "x2" = Some (RVal_Bits sp) ->
  regs !! "x10" = Some oldX10 ->
  global.(seq_instrs) !! Z_to_bv 64 0x15694 = Some a15694 ->
  global.(seq_instrs) !! Z_to_bv 64 0x15698 = Some a15698 ->
  eval_a_exp regs writeSuccess15694Mstatus = Some (Val_Bool true) ->
  IslaInstructionSegment (writeSuccess15694Before regs global)
    (writeSuccess15694Observations regs global sp)
    (writeSuccess15694After regs global sp) /\
  (writeSuccess15694After regs global sp).1.(seq_regs) =
    writeSuccess15694Regs regs sp /\
  (writeSuccess15694After regs global sp).2.(seq_mem) = global.(seq_mem) /\
  concat (map microLabels (writeSuccess15694Observations regs global sp)) = [].
Proof.
  intros Hpc Hsp Hx10 Hcode Hnext Hmstatus.
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

Lemma segment_15694 (regs : reg_map) (global : seq_global_state)
    (sp : bv 64) oldX10 :
  regs !! "PC" = Some (RVal_Bits (Z_to_bv 64 0x15694)) ->
  regs !! "x2" = Some (RVal_Bits sp) ->
  regs !! "x10" = Some oldX10 ->
  global.(seq_instrs) !! Z_to_bv 64 0x15694 = Some a15694 ->
  global.(seq_instrs) !! Z_to_bv 64 0x15698 = Some a15698 ->
  eval_a_exp regs writeSuccess15694Mstatus = Some (Val_Bool true) ->
  IslaInstructionSegment (writeSuccess15694Before regs global)
    (writeSuccess15694Observations regs global sp)
    (writeSuccess15694After regs global sp) /\
  (writeSuccess15694After regs global sp).1.(seq_regs) =
    writeSuccess15694Regs regs sp /\
  (writeSuccess15694After regs global sp).2.(seq_mem) = global.(seq_mem) /\
  concat (map microLabels (writeSuccess15694Observations regs global sp)) = [].
Proof.
  intros Hpc Hsp Hx10 Hcode Hnext Hmstatus.
  eapply segment_15694_mstatus; eauto.
Qed.

Print Assumptions writeSuccess15694NextPcExact.
Print Assumptions segment_15694_mstatus.
Print Assumptions segment_15694.
Print Assumptions writeSuccess15694RegsLookupOther.
