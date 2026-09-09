From Coq Require Import Lists.List ZArith.ZArith.
Require Import isla.riscv64.riscv64.
Require Import IslaTraces.write_success_02.a101d4.
Require Import IslaTraces.write_success_02.a101d8.
Require Import ZesuSsz.Contracts.InstructionBoundary.
Require Import ZesuSsz.Experiments.WriteSuccessSegmentAutomation.
Require Import ZesuSsz.Experiments.WriteSuccessCoverageAutomation.
Require Import ZesuSsz.Experiments.WriteSuccessSegment15694.

Import ListNotations.
Open Scope Z_scope.

Definition writeSuccess101d4Trace1 :=
  subst_trace (Val_Bits (BV 64 0)) 2 (writeSuccessTraceTail a101d4).
Definition writeSuccess101d4Trace2 := writeSuccessTraceTail writeSuccess101d4Trace1.
Definition writeSuccess101d4Trace3 :=
  subst_trace (Val_Bits (Z_to_bv 64 0x101d4)) 3
    (writeSuccessTraceTail writeSuccess101d4Trace2).
Definition writeSuccess101d4Trace4 := writeSuccessTraceTail writeSuccess101d4Trace3.
Definition writeSuccess101d4NextPc : bv 64 :=
  (Z_to_bv 64 0x101d4 + BV 64 4)%bv.
Definition writeSuccess101d4Trace5 :=
  subst_trace (Val_Bits writeSuccess101d4NextPc) 4
    (writeSuccessTraceTail writeSuccess101d4Trace4).
Definition writeSuccess101d4Trace6 := writeSuccessTraceTail writeSuccess101d4Trace5.
Definition writeSuccess101d4Trace7 := writeSuccessTraceTail writeSuccess101d4Trace6.

Definition writeSuccess101d4Regs (regs : reg_map) : reg_map :=
  <["PC" := RVal_Bits writeSuccess101d4NextPc]>
    (<["x15" := RVal_Bits (BV 64 0)]> regs).

Lemma writeSuccess101d4RegsLookupOther regs reg :
  reg <> "PC" ->
  reg <> "x15" ->
  writeSuccess101d4Regs regs !! reg = regs !! reg.
Proof.
  intros Hpc Hx12. unfold writeSuccess101d4Regs.
  rewrite lookup_insert_ne; last congruence.
  rewrite lookup_insert_ne; last congruence.
  reflexivity.
Qed.

Lemma writeSuccess101d4RegsDom regs oldX15 :
  regs !! "PC" = Some (RVal_Bits (Z_to_bv 64 0x101d4)) ->
  regs !! "x15" = Some oldX15 ->
  dom (writeSuccess101d4Regs regs) = dom regs.
Proof.
  intros Hpc Hx12.
  apply elem_of_dom_2 in Hpc. apply elem_of_dom_2 in Hx12.
  unfold writeSuccess101d4Regs. rewrite !dom_insert_L.
  set_solver.
Qed.

Definition writeSuccess101d4Before (regs : reg_map)
    (global : seq_global_state) : IslaState :=
  (writeSuccess15694Local a101d4 regs, global).

Definition writeSuccess101d4After (regs : reg_map)
    (global : seq_global_state) : IslaState :=
  (writeSuccess15694Local a101d8 (writeSuccess101d4Regs regs), global).

Lemma writeSuccess101d4NextPcExact :
  writeSuccess101d4NextPc = Z_to_bv 64 0x101d8.
Proof. unfold writeSuccess101d4NextPc. bv_solve. Qed.

Definition writeSuccess101d4PrefixObservations (regs : reg_map)
    (global : seq_global_state) : list IslaMicroObservation :=
  [writeSuccess15694Observation
     (writeSuccess15694Local writeSuccess101d4Trace1 regs) global;
   writeSuccess15694Observation
     (writeSuccess15694Local writeSuccess101d4Trace2 regs) global;
   writeSuccess15694Observation
     (writeSuccess15694Local writeSuccess101d4Trace3 regs) global;
   writeSuccess15694Observation
     (writeSuccess15694Local writeSuccess101d4Trace4 regs) global;
   writeSuccess15694Observation
     (writeSuccess15694Local writeSuccess101d4Trace5 regs) global;
   writeSuccess15694Observation
     (writeSuccess15694Local writeSuccess101d4Trace6
       (<["x15" := RVal_Bits (BV 64 0)]> regs)) global;
   writeSuccess15694Observation
     (writeSuccess15694Local writeSuccess101d4Trace7
       (writeSuccess101d4Regs regs)) global].

Definition writeSuccess101d4Observations (regs : reg_map)
    (global : seq_global_state) : list IslaMicroObservation :=
  writeSuccess101d4PrefixObservations regs global ++
  [writeSuccess15694Observation
     (writeSuccess101d4After regs global).1 global].

Lemma segment_101d4_mstatus (regs : reg_map) (global : seq_global_state) oldX15 :
  regs !! "PC" = Some (RVal_Bits (Z_to_bv 64 0x101d4)) ->
  regs !! "x15" = Some oldX15 ->
  global.(seq_instrs) !! Z_to_bv 64 0x101d4 = Some a101d4 ->
  global.(seq_instrs) !! Z_to_bv 64 0x101d8 = Some a101d8 ->
  eval_a_exp regs writeSuccess15694Mstatus = Some (Val_Bool true) ->
  IslaInstructionSegment (writeSuccess101d4Before regs global)
    (writeSuccess101d4Observations regs global)
    (writeSuccess101d4After regs global) /\
  (writeSuccess101d4After regs global).1.(seq_regs) =
    writeSuccess101d4Regs regs /\
  (writeSuccess101d4After regs global).2.(seq_mem) = global.(seq_mem) /\
  concat (map microLabels (writeSuccess101d4Observations regs global)) = [].
Proof.
  intros Hpc Hx12 Hcode Hnext Hmstatus.
  split; [|repeat split; reflexivity].
  unfold writeSuccess101d4Observations.
  eapply islaInstructionSegmentIntro with
    (done := (writeSuccess15694Local tnil (writeSuccess101d4Regs regs), global))
    (labels := []) (spawned := []).
  - split; first reflexivity. exists (Z_to_bv 64 0x101d4), a101d4.
    cbn. rewrite Hpc Hcode. repeat split; reflexivity.
  - unfold writeSuccess101d4PrefixObservations.
    eapply IslaInstructionPrefixStep; first discriminate.
    { apply writeSuccessSeqSilent; first reflexivity.
      unfold writeSuccess101d4Before, writeSuccess101d4Trace1,
        writeSuccessTraceTail, a101d4. cbn.
      apply DeclareConstBitVecS' with (b := BV 64 0). }
    eapply IslaInstructionPrefixStep; first discriminate.
    { apply writeSuccessSeqAssume; first reflexivity.
      unfold writeSuccess101d4Trace1, writeSuccessTraceTail, a101d4. cbn.
      eapply AssumeS. exact Hmstatus. }
    eapply IslaInstructionPrefixStep; first discriminate.
    { apply writeSuccessSeqSilent; first reflexivity.
      unfold writeSuccess101d4Trace2, writeSuccess101d4Trace1,
        writeSuccessTraceTail, a101d4. cbn.
      apply DeclareConstBitVecS' with (b := Z_to_bv 64 0x101d4). }
    eapply IslaInstructionPrefixStep; first discriminate.
    { eapply writeSuccessSeqReadReg with
        (root := RVal_Bits (Z_to_bv 64 0x101d4))
        (value := RVal_Bits (Z_to_bv 64 0x101d4)).
      - reflexivity.
      - unfold writeSuccess101d4Trace3, writeSuccess101d4Trace2,
          writeSuccess101d4Trace1, writeSuccessTraceTail, a101d4. cbn.
        constructor.
      - exact Hpc.
      - reflexivity.
      - reflexivity. }
    eapply IslaInstructionPrefixStep; first discriminate.
    { apply writeSuccessSeqSilent; first reflexivity.
      unfold writeSuccess101d4Trace5, writeSuccess101d4Trace4,
        writeSuccess101d4Trace3, writeSuccess101d4Trace2,
        writeSuccess101d4Trace1, writeSuccess101d4NextPc,
        writeSuccessTraceTail, a101d4. cbn.
      eapply DefineConstS with
        (v := Val_Bits (Z_to_bv 64 0x101d4 + BV 64 4)%bv).
      reflexivity. }
    eapply IslaInstructionPrefixStep; first discriminate.
    { eapply writeSuccessSeqWriteReg with (root := oldX15)
        (value := RVal_Bits (BV 64 0))
        (updated := RVal_Bits (BV 64 0)).
      - reflexivity.
      - unfold writeSuccess101d4Trace5, writeSuccess101d4Trace4,
          writeSuccess101d4Trace3, writeSuccess101d4Trace2,
          writeSuccess101d4Trace1, writeSuccessTraceTail, a101d4. cbn.
        constructor.
      - exact Hx12.
      - reflexivity.
      - reflexivity. }
    eapply IslaInstructionPrefixStep; first discriminate.
    { eapply writeSuccessSeqWriteReg with
        (root := RVal_Bits (Z_to_bv 64 0x101d4))
        (value := RVal_Bits writeSuccess101d4NextPc)
        (updated := RVal_Bits writeSuccess101d4NextPc).
      - reflexivity.
      - unfold writeSuccess101d4Trace6, writeSuccess101d4Trace5,
          writeSuccess101d4Trace4, writeSuccess101d4Trace3,
          writeSuccess101d4Trace2, writeSuccess101d4Trace1,
          writeSuccessTraceTail, a101d4. cbn. constructor.
      - rewrite lookup_insert_ne; last done. exact Hpc.
      - reflexivity.
      - reflexivity. }
    apply IslaInstructionPrefixRefl.
  - reflexivity.
  - apply writeSuccessSeqDoneTabled with (next := a101d8) (trace := a101d8).
    + reflexivity.
    + reflexivity.
    + constructor.
    + exists (Z_to_bv 64 0x101d8).
      unfold writeSuccess101d4Regs. rewrite lookup_insert.
      rewrite writeSuccess101d4NextPcExact Hnext.
      repeat split; reflexivity.
  - left. split; first reflexivity. exists (Z_to_bv 64 0x101d8), a101d8.
    cbn. unfold writeSuccess101d4Regs. rewrite lookup_insert.
    rewrite writeSuccess101d4NextPcExact Hnext.
    repeat split; reflexivity.
Qed.

Lemma segment_101d4 (regs : reg_map) (global : seq_global_state) oldX15 :
  regs !! "PC" = Some (RVal_Bits (Z_to_bv 64 0x101d4)) ->
  regs !! "x15" = Some oldX15 ->
  global.(seq_instrs) !! Z_to_bv 64 0x101d4 = Some a101d4 ->
  global.(seq_instrs) !! Z_to_bv 64 0x101d8 = Some a101d8 ->
  eval_a_exp regs writeSuccess15694Mstatus = Some (Val_Bool true) ->
  IslaInstructionSegment (writeSuccess101d4Before regs global)
    (writeSuccess101d4Observations regs global)
    (writeSuccess101d4After regs global) /\
  (writeSuccess101d4After regs global).1.(seq_regs) =
    writeSuccess101d4Regs regs /\
  (writeSuccess101d4After regs global).2.(seq_mem) = global.(seq_mem) /\
  concat (map microLabels (writeSuccess101d4Observations regs global)) = [].
Proof.
  intros Hpc Hx12 Hcode Hnext Hmstatus.
  eapply segment_101d4_mstatus; eauto.
Qed.

Print Assumptions segment_101d4_mstatus.
Print Assumptions segment_101d4.
Print Assumptions writeSuccess101d4RegsLookupOther.
Print Assumptions writeSuccess101d4RegsDom.
