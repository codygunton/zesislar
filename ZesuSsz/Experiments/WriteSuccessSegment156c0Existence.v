From Coq Require Import Lists.List ZArith.ZArith.
Require Import isla.riscv64.riscv64.
Require Import IslaTraces.write_success_93.a156c0.
Require Import IslaTraces.write_success_93.a156c4.
Require Import ZesuSsz.Contracts.InstructionBoundary.
Require Import ZesuSsz.Experiments.WriteSuccessSegmentAutomation.
Require Import ZesuSsz.Experiments.WriteSuccessCoverageAutomation.
Require Import ZesuSsz.Experiments.WriteSuccessSegment15694.

Import ListNotations.
Open Scope Z_scope.

Definition writeSuccess156c0Trace1 :=
  subst_trace (Val_Bits (BV 64 0)) 2 (writeSuccessTraceTail a156c0).
Definition writeSuccess156c0Trace2 := writeSuccessTraceTail writeSuccess156c0Trace1.
Definition writeSuccess156c0Trace3 :=
  subst_trace (Val_Bits (Z_to_bv 64 0x156c0)) 3
    (writeSuccessTraceTail writeSuccess156c0Trace2).
Definition writeSuccess156c0Trace4 := writeSuccessTraceTail writeSuccess156c0Trace3.
Definition writeSuccess156c0NextPc : bv 64 :=
  (Z_to_bv 64 0x156c0 + BV 64 4)%bv.
Definition writeSuccess156c0Trace5 :=
  subst_trace (Val_Bits writeSuccess156c0NextPc) 4
    (writeSuccessTraceTail writeSuccess156c0Trace4).
Definition writeSuccess156c0Trace6 := writeSuccessTraceTail writeSuccess156c0Trace5.
Definition writeSuccess156c0Trace7 := writeSuccessTraceTail writeSuccess156c0Trace6.

Definition writeSuccess156c0Regs (regs : reg_map) : reg_map :=
  <["PC" := RVal_Bits writeSuccess156c0NextPc]>
    (<["x11" := RVal_Bits (BV 64 20)]> regs).

Lemma writeSuccess156c0RegsLookupOther regs reg :
  reg <> "PC" ->
  reg <> "x11" ->
  writeSuccess156c0Regs regs !! reg = regs !! reg.
Proof.
  intros Hpc Hx12. unfold writeSuccess156c0Regs.
  rewrite lookup_insert_ne; last congruence.
  rewrite lookup_insert_ne; last congruence.
  reflexivity.
Qed.

Lemma writeSuccess156c0RegsDom regs oldX11 :
  regs !! "PC" = Some (RVal_Bits (Z_to_bv 64 0x156c0)) ->
  regs !! "x11" = Some oldX11 ->
  dom (writeSuccess156c0Regs regs) = dom regs.
Proof.
  intros Hpc Hx12.
  apply elem_of_dom_2 in Hpc. apply elem_of_dom_2 in Hx12.
  unfold writeSuccess156c0Regs. rewrite !dom_insert_L.
  set_solver.
Qed.

Definition writeSuccess156c0Before (regs : reg_map)
    (global : seq_global_state) : IslaState :=
  (writeSuccess15694Local a156c0 regs, global).

Definition writeSuccess156c0After (regs : reg_map)
    (global : seq_global_state) : IslaState :=
  (writeSuccess15694Local a156c4 (writeSuccess156c0Regs regs), global).

Lemma writeSuccess156c0NextPcExact :
  writeSuccess156c0NextPc = Z_to_bv 64 0x156c4.
Proof. unfold writeSuccess156c0NextPc. bv_solve. Qed.

Definition writeSuccess156c0PrefixObservations (regs : reg_map)
    (global : seq_global_state) : list IslaMicroObservation :=
  [writeSuccess15694Observation
     (writeSuccess15694Local writeSuccess156c0Trace1 regs) global;
   writeSuccess15694Observation
     (writeSuccess15694Local writeSuccess156c0Trace2 regs) global;
   writeSuccess15694Observation
     (writeSuccess15694Local writeSuccess156c0Trace3 regs) global;
   writeSuccess15694Observation
     (writeSuccess15694Local writeSuccess156c0Trace4 regs) global;
   writeSuccess15694Observation
     (writeSuccess15694Local writeSuccess156c0Trace5 regs) global;
   writeSuccess15694Observation
     (writeSuccess15694Local writeSuccess156c0Trace6
       (<["x11" := RVal_Bits (BV 64 20)]> regs)) global;
   writeSuccess15694Observation
     (writeSuccess15694Local writeSuccess156c0Trace7
       (writeSuccess156c0Regs regs)) global].

Definition writeSuccess156c0Observations (regs : reg_map)
    (global : seq_global_state) : list IslaMicroObservation :=
  writeSuccess156c0PrefixObservations regs global ++
  [writeSuccess15694Observation
     (writeSuccess156c0After regs global).1 global].

Lemma segment_156c0_mstatus (regs : reg_map) (global : seq_global_state) oldX11 :
  regs !! "PC" = Some (RVal_Bits (Z_to_bv 64 0x156c0)) ->
  regs !! "x11" = Some oldX11 ->
  global.(seq_instrs) !! Z_to_bv 64 0x156c0 = Some a156c0 ->
  global.(seq_instrs) !! Z_to_bv 64 0x156c4 = Some a156c4 ->
  eval_a_exp regs writeSuccess15694Mstatus = Some (Val_Bool true) ->
  IslaInstructionSegment (writeSuccess156c0Before regs global)
    (writeSuccess156c0Observations regs global)
    (writeSuccess156c0After regs global) /\
  (writeSuccess156c0After regs global).1.(seq_regs) =
    writeSuccess156c0Regs regs /\
  (writeSuccess156c0After regs global).2.(seq_mem) = global.(seq_mem) /\
  concat (map microLabels (writeSuccess156c0Observations regs global)) = [].
Proof.
  intros Hpc Hx12 Hcode Hnext Hmstatus.
  split; [|repeat split; reflexivity].
  unfold writeSuccess156c0Observations.
  eapply islaInstructionSegmentIntro with
    (done := (writeSuccess15694Local tnil (writeSuccess156c0Regs regs), global))
    (labels := []) (spawned := []).
  - split; first reflexivity. exists (Z_to_bv 64 0x156c0), a156c0.
    cbn. rewrite Hpc Hcode. repeat split; reflexivity.
  - unfold writeSuccess156c0PrefixObservations.
    eapply IslaInstructionPrefixStep; first discriminate.
    { apply writeSuccessSeqSilent; first reflexivity.
      unfold writeSuccess156c0Before, writeSuccess156c0Trace1,
        writeSuccessTraceTail, a156c0. cbn.
      apply DeclareConstBitVecS' with (b := BV 64 0). }
    eapply IslaInstructionPrefixStep; first discriminate.
    { apply writeSuccessSeqAssume; first reflexivity.
      unfold writeSuccess156c0Trace1, writeSuccessTraceTail, a156c0. cbn.
      eapply AssumeS. exact Hmstatus. }
    eapply IslaInstructionPrefixStep; first discriminate.
    { apply writeSuccessSeqSilent; first reflexivity.
      unfold writeSuccess156c0Trace2, writeSuccess156c0Trace1,
        writeSuccessTraceTail, a156c0. cbn.
      apply DeclareConstBitVecS' with (b := Z_to_bv 64 0x156c0). }
    eapply IslaInstructionPrefixStep; first discriminate.
    { eapply writeSuccessSeqReadReg with
        (root := RVal_Bits (Z_to_bv 64 0x156c0))
        (value := RVal_Bits (Z_to_bv 64 0x156c0)).
      - reflexivity.
      - unfold writeSuccess156c0Trace3, writeSuccess156c0Trace2,
          writeSuccess156c0Trace1, writeSuccessTraceTail, a156c0. cbn.
        constructor.
      - exact Hpc.
      - reflexivity.
      - reflexivity. }
    eapply IslaInstructionPrefixStep; first discriminate.
    { apply writeSuccessSeqSilent; first reflexivity.
      unfold writeSuccess156c0Trace5, writeSuccess156c0Trace4,
        writeSuccess156c0Trace3, writeSuccess156c0Trace2,
        writeSuccess156c0Trace1, writeSuccess156c0NextPc,
        writeSuccessTraceTail, a156c0. cbn.
      eapply DefineConstS with
        (v := Val_Bits (Z_to_bv 64 0x156c0 + BV 64 4)%bv).
      reflexivity. }
    eapply IslaInstructionPrefixStep; first discriminate.
    { eapply writeSuccessSeqWriteReg with (root := oldX11)
        (value := RVal_Bits (BV 64 20))
        (updated := RVal_Bits (BV 64 20)).
      - reflexivity.
      - unfold writeSuccess156c0Trace5, writeSuccess156c0Trace4,
          writeSuccess156c0Trace3, writeSuccess156c0Trace2,
          writeSuccess156c0Trace1, writeSuccessTraceTail, a156c0. cbn.
        constructor.
      - exact Hx12.
      - reflexivity.
      - reflexivity. }
    eapply IslaInstructionPrefixStep; first discriminate.
    { eapply writeSuccessSeqWriteReg with
        (root := RVal_Bits (Z_to_bv 64 0x156c0))
        (value := RVal_Bits writeSuccess156c0NextPc)
        (updated := RVal_Bits writeSuccess156c0NextPc).
      - reflexivity.
      - unfold writeSuccess156c0Trace6, writeSuccess156c0Trace5,
          writeSuccess156c0Trace4, writeSuccess156c0Trace3,
          writeSuccess156c0Trace2, writeSuccess156c0Trace1,
          writeSuccessTraceTail, a156c0. cbn. constructor.
      - rewrite lookup_insert_ne; last done. exact Hpc.
      - reflexivity.
      - reflexivity. }
    apply IslaInstructionPrefixRefl.
  - reflexivity.
  - apply writeSuccessSeqDoneTabled with (next := a156c4) (trace := a156c4).
    + reflexivity.
    + reflexivity.
    + constructor.
    + exists (Z_to_bv 64 0x156c4).
      unfold writeSuccess156c0Regs. rewrite lookup_insert.
      rewrite writeSuccess156c0NextPcExact Hnext.
      repeat split; reflexivity.
  - left. split; first reflexivity. exists (Z_to_bv 64 0x156c4), a156c4.
    cbn. unfold writeSuccess156c0Regs. rewrite lookup_insert.
    rewrite writeSuccess156c0NextPcExact Hnext.
    repeat split; reflexivity.
Qed.

Lemma segment_156c0 (regs : reg_map) (global : seq_global_state) oldX11 :
  regs !! "PC" = Some (RVal_Bits (Z_to_bv 64 0x156c0)) ->
  regs !! "x11" = Some oldX11 ->
  global.(seq_instrs) !! Z_to_bv 64 0x156c0 = Some a156c0 ->
  global.(seq_instrs) !! Z_to_bv 64 0x156c4 = Some a156c4 ->
  eval_a_exp regs writeSuccess15694Mstatus = Some (Val_Bool true) ->
  IslaInstructionSegment (writeSuccess156c0Before regs global)
    (writeSuccess156c0Observations regs global)
    (writeSuccess156c0After regs global) /\
  (writeSuccess156c0After regs global).1.(seq_regs) =
    writeSuccess156c0Regs regs /\
  (writeSuccess156c0After regs global).2.(seq_mem) = global.(seq_mem) /\
  concat (map microLabels (writeSuccess156c0Observations regs global)) = [].
Proof.
  intros Hpc Hx12 Hcode Hnext Hmstatus.
  eapply segment_156c0_mstatus; eauto.
Qed.

Print Assumptions segment_156c0_mstatus.
Print Assumptions segment_156c0.
Print Assumptions writeSuccess156c0RegsLookupOther.
Print Assumptions writeSuccess156c0RegsDom.
