From Coq Require Import Eqdep_dec Lists.List ZArith.ZArith.
Require Import isla.riscv64.riscv64.
Require Import IslaTraces.write_success_90.a1569c.
Require Import IslaTraces.write_success_90.a156a0.
Require Import ZesuSsz.Contracts.InstructionBoundary.
Require Import ZesuSsz.Experiments.WriteSuccessSegmentAutomation.
Require Import ZesuSsz.Experiments.WriteSuccessCoverageAutomation.

Import ListNotations.
Open Scope Z_scope.

Definition writeSuccessTraceTail (trace : isla_trace) : isla_trace :=
  match trace with tcons _ rest => rest | _ => tnil end.

Definition writeSuccess1569cMstatus : a_exp :=
  AExp_Binop Eq
    (AExp_Manyop (Bvmanyarith Bvand)
      [AExp_Val (AVal_Var "mstatus" [Field "bits"]) Mk_annot;
       AExp_Val (AVal_Bits (BV 64 0x20000)) Mk_annot] Mk_annot)
    (AExp_Val (AVal_Bits (BV 64 0)) Mk_annot) Mk_annot.

Definition writeSuccess1569cTrace1 :=
  subst_trace (Val_Bits (BV 64 0)) 2 (writeSuccessTraceTail a1569c).
Definition writeSuccess1569cTrace2 := writeSuccessTraceTail writeSuccess1569cTrace1.
Definition writeSuccess1569cTrace3 :=
  subst_trace (Val_Bits (Z_to_bv 64 0x1569c)) 3
    (writeSuccessTraceTail writeSuccess1569cTrace2).
Definition writeSuccess1569cTrace4 := writeSuccessTraceTail writeSuccess1569cTrace3.
Definition writeSuccess1569cNextPc : bv 64 :=
  (Z_to_bv 64 0x1569c + BV 64 4)%bv.
Definition writeSuccess1569cTrace5 :=
  subst_trace (Val_Bits writeSuccess1569cNextPc) 4
    (writeSuccessTraceTail writeSuccess1569cTrace4).
Definition writeSuccess1569cTrace6 (sp : bv 64) :=
  subst_trace (Val_Bits sp) 5 (writeSuccessTraceTail writeSuccess1569cTrace5).
Definition writeSuccess1569cTrace7 (sp : bv 64) :=
  writeSuccessTraceTail (writeSuccess1569cTrace6 sp).
Definition writeSuccess1569cTrace8 (sp : bv 64) :=
  subst_trace (Val_Bits (sp + BV 64 0)%bv) 6
    (writeSuccessTraceTail (writeSuccess1569cTrace7 sp)).
Definition writeSuccess1569cTrace9 (sp : bv 64) :=
  writeSuccessTraceTail (writeSuccess1569cTrace8 sp).
Definition writeSuccess1569cTrace10 (sp : bv 64) :=
  writeSuccessTraceTail (writeSuccess1569cTrace9 sp).

Definition writeSuccess1569cRegs (regs : reg_map) (sp : bv 64) : reg_map :=
  <["PC" := RVal_Bits writeSuccess1569cNextPc]>
    (<["x11" := RVal_Bits (sp + BV 64 0)%bv]> regs).

Lemma writeSuccess1569cRegsLookupOther regs sp reg :
  reg <> "PC" ->
  reg <> "x11" ->
  writeSuccess1569cRegs regs sp !! reg = regs !! reg.
Proof.
  intros Hpc Hx10. unfold writeSuccess1569cRegs.
  rewrite lookup_insert_ne; last congruence.
  rewrite lookup_insert_ne; last congruence.
  reflexivity.
Qed.

Definition writeSuccess1569cLocal (trace : isla_trace) (regs : reg_map) :
    seq_local_state := {|
  seq_trace := trace;
  seq_regs := regs;
  seq_pc_reg := "PC";
  seq_nb_state := false
|}.

Definition writeSuccess1569cBefore (regs : reg_map)
    (global : seq_global_state) : IslaState :=
  (writeSuccess1569cLocal a1569c regs, global).

Definition writeSuccess1569cAfter (regs : reg_map) (global : seq_global_state)
    (sp : bv 64) : IslaState :=
  (writeSuccess1569cLocal a156a0 (writeSuccess1569cRegs regs sp), global).

Definition writeSuccess1569cObservation (local : seq_local_state)
    (global : seq_global_state) : IslaMicroObservation := {|
  microLabels := [];
  microAfter := (local, global)
|}.

Lemma writeSuccess1569cNextPcExact :
  writeSuccess1569cNextPc = Z_to_bv 64 0x156a0.
Proof. unfold writeSuccess1569cNextPc. bv_solve. Qed.

Definition writeSuccess1569cPrefixObservations (regs : reg_map)
    (global : seq_global_state) (sp : bv 64) : list IslaMicroObservation :=
  [writeSuccess1569cObservation
     (writeSuccess1569cLocal writeSuccess1569cTrace1 regs) global;
   writeSuccess1569cObservation
     (writeSuccess1569cLocal writeSuccess1569cTrace2 regs) global;
   writeSuccess1569cObservation
     (writeSuccess1569cLocal writeSuccess1569cTrace3 regs) global;
   writeSuccess1569cObservation
     (writeSuccess1569cLocal writeSuccess1569cTrace4 regs) global;
   writeSuccess1569cObservation
     (writeSuccess1569cLocal writeSuccess1569cTrace5 regs) global;
   writeSuccess1569cObservation
     (writeSuccess1569cLocal (writeSuccess1569cTrace6 sp) regs) global;
   writeSuccess1569cObservation
     (writeSuccess1569cLocal (writeSuccess1569cTrace7 sp) regs) global;
   writeSuccess1569cObservation
     (writeSuccess1569cLocal (writeSuccess1569cTrace8 sp) regs) global;
   writeSuccess1569cObservation
     (writeSuccess1569cLocal (writeSuccess1569cTrace9 sp)
       (<["x11" := RVal_Bits (sp + BV 64 0)%bv]> regs)) global;
   writeSuccess1569cObservation
     (writeSuccess1569cLocal (writeSuccess1569cTrace10 sp)
       (writeSuccess1569cRegs regs sp)) global].

Definition writeSuccess1569cObservations (regs : reg_map)
    (global : seq_global_state) (sp : bv 64) : list IslaMicroObservation :=
  writeSuccess1569cPrefixObservations regs global sp ++
  [writeSuccess1569cObservation
     (writeSuccess1569cAfter regs global sp).1 global].

Lemma writeSuccess1569cTakeStep before observations done :
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

Lemma segment_1569c_mstatus (regs : reg_map) (global : seq_global_state)
    (sp : bv 64) oldX11 :
  regs !! "PC" = Some (RVal_Bits (Z_to_bv 64 0x1569c)) ->
  regs !! "x8" = Some (RVal_Bits sp) ->
  regs !! "x11" = Some oldX11 ->
  global.(seq_instrs) !! Z_to_bv 64 0x1569c = Some a1569c ->
  global.(seq_instrs) !! Z_to_bv 64 0x156a0 = Some a156a0 ->
  eval_a_exp regs writeSuccess1569cMstatus = Some (Val_Bool true) ->
  IslaInstructionSegment (writeSuccess1569cBefore regs global)
    (writeSuccess1569cObservations regs global sp)
    (writeSuccess1569cAfter regs global sp) /\
  (writeSuccess1569cAfter regs global sp).1.(seq_regs) =
    writeSuccess1569cRegs regs sp /\
  (writeSuccess1569cAfter regs global sp).2.(seq_mem) = global.(seq_mem) /\
  concat (map microLabels (writeSuccess1569cObservations regs global sp)) = [].
Proof.
  intros Hpc Hsp Hx10 Hcode Hnext Hmstatus.
  split; [|repeat split; reflexivity].
  unfold writeSuccess1569cObservations.
  eapply islaInstructionSegmentIntro with
    (done := (writeSuccess1569cLocal tnil (writeSuccess1569cRegs regs sp), global))
    (labels := []) (spawned := []).
  - split; first reflexivity. exists (Z_to_bv 64 0x1569c), a1569c.
    cbn. rewrite Hpc Hcode. repeat split; reflexivity.
  - unfold writeSuccess1569cPrefixObservations.
    eapply IslaInstructionPrefixStep; first discriminate.
    { apply writeSuccessSeqSilent; first reflexivity.
      unfold writeSuccess1569cBefore, writeSuccess1569cLocal,
        writeSuccess1569cTrace1, writeSuccessTraceTail, a1569c. cbn.
      apply DeclareConstBitVecS' with (b := BV 64 0). }
    eapply IslaInstructionPrefixStep; first discriminate.
    { apply writeSuccessSeqAssume; first reflexivity.
      unfold writeSuccess1569cTrace1, writeSuccessTraceTail, a1569c. cbn.
      eapply AssumeS. exact Hmstatus. }
    eapply IslaInstructionPrefixStep; first discriminate.
    { apply writeSuccessSeqSilent; first reflexivity.
      unfold writeSuccess1569cTrace2, writeSuccess1569cTrace1,
        writeSuccessTraceTail, a1569c. cbn.
      apply DeclareConstBitVecS' with (b := Z_to_bv 64 0x1569c). }
    eapply IslaInstructionPrefixStep; first discriminate.
    { eapply writeSuccessSeqReadReg with
        (root := RVal_Bits (Z_to_bv 64 0x1569c))
        (value := RVal_Bits (Z_to_bv 64 0x1569c)).
      - reflexivity.
      - unfold writeSuccess1569cTrace3, writeSuccess1569cTrace2,
          writeSuccess1569cTrace1, writeSuccessTraceTail, a1569c. cbn.
        constructor.
      - exact Hpc.
      - reflexivity.
      - reflexivity. }
    eapply IslaInstructionPrefixStep; first discriminate.
    { apply writeSuccessSeqSilent; first reflexivity.
      unfold writeSuccess1569cTrace5, writeSuccess1569cTrace4, writeSuccess1569cTrace3,
        writeSuccess1569cTrace2, writeSuccess1569cTrace1,
        writeSuccess1569cNextPc, writeSuccessTraceTail, a1569c. cbn.
      eapply DefineConstS with
        (v := Val_Bits (Z_to_bv 64 0x1569c + BV 64 4)%bv).
      reflexivity. }
    eapply IslaInstructionPrefixStep; first discriminate.
    { apply writeSuccessSeqSilent; first reflexivity.
      unfold writeSuccess1569cTrace5, writeSuccess1569cTrace4,
        writeSuccess1569cTrace3, writeSuccess1569cTrace2,
        writeSuccess1569cTrace1, writeSuccessTraceTail, a1569c. cbn.
      apply DeclareConstBitVecS' with (b := sp). }
    eapply IslaInstructionPrefixStep; first discriminate.
    { eapply writeSuccessSeqReadReg with
        (root := RVal_Bits sp) (value := RVal_Bits sp).
      - reflexivity.
      - unfold writeSuccess1569cTrace6, writeSuccess1569cTrace5,
          writeSuccess1569cTrace4, writeSuccess1569cTrace3,
          writeSuccess1569cTrace2, writeSuccess1569cTrace1,
          writeSuccessTraceTail, a1569c. cbn. constructor.
      - exact Hsp.
      - reflexivity.
      - reflexivity. }
    eapply IslaInstructionPrefixStep; first discriminate.
    { apply writeSuccessSeqSilent; first reflexivity.
      unfold writeSuccess1569cTrace7, writeSuccess1569cTrace6,
        writeSuccess1569cTrace5, writeSuccess1569cTrace4,
        writeSuccess1569cTrace3, writeSuccess1569cTrace2,
        writeSuccess1569cTrace1, writeSuccessTraceTail, a1569c. cbn.
      eapply DefineConstS with (v := Val_Bits (sp + BV 64 0)%bv).
      reflexivity. }
    eapply IslaInstructionPrefixStep; first discriminate.
    { eapply writeSuccessSeqWriteReg with (root := oldX11)
        (value := RVal_Bits (sp + BV 64 0)%bv)
        (updated := RVal_Bits (sp + BV 64 0)%bv).
      - reflexivity.
      - unfold writeSuccess1569cTrace8, writeSuccess1569cTrace7,
          writeSuccess1569cTrace6, writeSuccess1569cTrace5,
          writeSuccess1569cTrace4, writeSuccess1569cTrace3,
          writeSuccess1569cTrace2, writeSuccess1569cTrace1,
          writeSuccessTraceTail, a1569c. cbn. constructor.
      - exact Hx10.
      - reflexivity.
      - reflexivity. }
    eapply IslaInstructionPrefixStep; first discriminate.
    { eapply writeSuccessSeqWriteReg with
        (root := RVal_Bits (Z_to_bv 64 0x1569c))
        (value := RVal_Bits writeSuccess1569cNextPc)
        (updated := RVal_Bits writeSuccess1569cNextPc).
      - reflexivity.
      - unfold writeSuccess1569cTrace9, writeSuccess1569cTrace8,
          writeSuccess1569cTrace7, writeSuccess1569cTrace6,
          writeSuccess1569cTrace5, writeSuccess1569cTrace4,
          writeSuccess1569cTrace3, writeSuccess1569cTrace2,
          writeSuccess1569cTrace1, writeSuccessTraceTail, a1569c. cbn.
        constructor.
      - rewrite lookup_insert_ne; last done. exact Hpc.
      - reflexivity.
      - reflexivity. }
    apply IslaInstructionPrefixRefl.
  - reflexivity.
  - apply writeSuccessSeqDoneTabled with (next := a156a0) (trace := a156a0).
    + reflexivity.
    + reflexivity.
    + constructor.
    + exists (Z_to_bv 64 0x156a0).
      unfold writeSuccess1569cRegs. rewrite lookup_insert.
      rewrite writeSuccess1569cNextPcExact Hnext.
      repeat split; reflexivity.
  - left. split; first reflexivity. exists (Z_to_bv 64 0x156a0), a156a0.
    cbn. unfold writeSuccess1569cRegs. rewrite lookup_insert.
    rewrite writeSuccess1569cNextPcExact Hnext.
    repeat split; reflexivity.
Qed.

Lemma segment_1569c (regs : reg_map) (global : seq_global_state)
    (sp : bv 64) oldX11 :
  regs !! "PC" = Some (RVal_Bits (Z_to_bv 64 0x1569c)) ->
  regs !! "x8" = Some (RVal_Bits sp) ->
  regs !! "x11" = Some oldX11 ->
  global.(seq_instrs) !! Z_to_bv 64 0x1569c = Some a1569c ->
  global.(seq_instrs) !! Z_to_bv 64 0x156a0 = Some a156a0 ->
  eval_a_exp regs writeSuccess1569cMstatus = Some (Val_Bool true) ->
  IslaInstructionSegment (writeSuccess1569cBefore regs global)
    (writeSuccess1569cObservations regs global sp)
    (writeSuccess1569cAfter regs global sp) /\
  (writeSuccess1569cAfter regs global sp).1.(seq_regs) =
    writeSuccess1569cRegs regs sp /\
  (writeSuccess1569cAfter regs global sp).2.(seq_mem) = global.(seq_mem) /\
  concat (map microLabels (writeSuccess1569cObservations regs global sp)) = [].
Proof.
  intros Hpc Hsp Hx10 Hcode Hnext Hmstatus.
  eapply segment_1569c_mstatus; eauto.
Qed.

Print Assumptions writeSuccess1569cNextPcExact.
Print Assumptions segment_1569c_mstatus.
Print Assumptions segment_1569c.
Print Assumptions writeSuccess1569cRegsLookupOther.
