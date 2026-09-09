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


Definition writeSuccess156a0First5Observations regs global :=
  firstn 5 (writeSuccess156a0PrefixObservations regs global).

Definition writeSuccess156a0TailObservations regs global :=
  skipn 5 (writeSuccess156a0PrefixObservations regs global).

Lemma writeSuccess156a0PrefixObservationsSplit regs global :
  writeSuccess156a0PrefixObservations regs global =
    writeSuccess156a0First5Observations regs global ++
    writeSuccess156a0TailObservations regs global.
Proof.
  unfold writeSuccess156a0PrefixObservations,
    writeSuccess156a0First5Observations,
    writeSuccess156a0TailObservations. cbn. reflexivity.
Qed.

Lemma writeSuccess156a0PrefixPathAppend before first middle second after :
  IslaInstructionPrefixPath before first middle ->
  IslaInstructionPrefixPath middle second after ->
  IslaInstructionPrefixPath before (first ++ second) after.
Proof.
  intros Hfirst Hsecond. induction Hfirst; cbn; first exact Hsecond.
  econstructor; eauto.
Qed.

Print Assumptions writeSuccess156a0PrefixObservationsSplit.
Print Assumptions writeSuccess156a0PrefixPathAppend.
