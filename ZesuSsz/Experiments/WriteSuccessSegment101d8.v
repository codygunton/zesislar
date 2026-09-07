From Coq Require Import Eqdep_dec Lists.List ZArith.ZArith.
Require Import isla.riscv64.riscv64.
Require Import IslaTraces.write_success_02.a101d8.
Require Import IslaTraces.write_success_02.a101dc.
Require Import IslaTraces.write_success_02.a101e0.
Require Import ZesuSsz.Contracts.InstructionBoundary.
Require Import ZesuSsz.Experiments.WriteSuccessSegmentAutomation.
Require Import ZesuSsz.Experiments.WriteSuccessCoverageAutomation.
Require Import ZesuSsz.Experiments.WriteSuccessTraceAssumptions.
Require Import ZesuSsz.Experiments.WriteSuccessSegment15694.

Import ListNotations.
Open Scope Z_scope.

Definition writeSuccess101d8Alignment : a_exp :=
  AExp_Binop Eq
    (AExp_Unop (Extract 1 0) (AExp_Val (AVal_Var "PC" []) Mk_annot) Mk_annot)
    (AExp_Val (AVal_Bits (BV 2 0)) Mk_annot) Mk_annot.

Definition writeSuccess101d8Condition (left right : bv 64) : exp :=
  Unop Not
    (Binop Eq (Val (Val_Bits left) Mk_annot)
      (Val (Val_Bits right) Mk_annot) Mk_annot) Mk_annot.

Lemma writeSuccessBvnToBvSame n (value : bv n) :
  bvn_to_bv n (bv_to_bvn value) = Some value.
Proof.
  destruct value as [bits Hbits]. unfold bvn_to_bv. cbn.
  destruct (decide (n = n)) as [Heq|Hneq].
  - f_equal. symmetry. apply Eqdep_dec.eq_rect_eq_dec. apply N.eq_dec.
  - exfalso. apply Hneq. reflexivity.
Qed.

Local Opaque bvn_to_bv.

Lemma writeSuccess101d8AlignmentHolds regs :
  regs !! "PC" = Some (RVal_Bits (Z_to_bv 64 0x101d8)) ->
  eval_a_exp regs writeSuccess101d8Alignment = Some (Val_Bool true).
Proof.
  intros Hpc. unfold writeSuccess101d8Alignment. cbn. rewrite Hpc. vm_compute.
  reflexivity.
Qed.

Lemma writeSuccess101d8ConditionTaken left right :
  left <> right ->
  eval_exp (writeSuccess101d8Condition left right) = Some (Val_Bool true).
Proof.
  intros Hne. unfold writeSuccess101d8Condition. cbn.
  rewrite writeSuccessBvnToBvSame. cbn.
  case_bool_decide; first contradiction. reflexivity.
Qed.

Lemma writeSuccess101d8ConditionFallthrough left right :
  left = right ->
  eval_exp (writeSuccess101d8Condition left right) = Some (Val_Bool false).
Proof.
  intros ->. unfold writeSuccess101d8Condition. cbn.
  rewrite writeSuccessBvnToBvSame. cbn.
  case_bool_decide; last contradiction. reflexivity.
Qed.

Print Assumptions writeSuccess101d8AlignmentHolds.
Print Assumptions writeSuccess101d8ConditionTaken.
Print Assumptions writeSuccess101d8ConditionFallthrough.

Definition writeSuccess101d8NextPc : bv 64 :=
  (Z_to_bv 64 0x101d8 + BV 64 4)%bv.
Definition writeSuccess101d8TakenPc : bv 64 :=
  (Z_to_bv 64 0x101d8 + BV 64 8)%bv.

Definition writeSuccess101d8Trace1 (condition : bool) :=
  subst_trace (Val_Bits (BV 64 0)) 2 (writeSuccessTraceTail a101d8).
Definition writeSuccess101d8Trace2 (condition : bool) :=
  writeSuccessTraceTail (writeSuccess101d8Trace1 condition).
Definition writeSuccess101d8Trace3 (condition : bool) :=
  subst_trace (Val_Bits (Z_to_bv 64 0x101d8)) 3
    (writeSuccessTraceTail (writeSuccess101d8Trace2 condition)).
Definition writeSuccess101d8Trace4 (condition : bool) :=
  writeSuccessTraceTail (writeSuccess101d8Trace3 condition).
Definition writeSuccess101d8Trace5 (condition : bool) :=
  writeSuccessTraceTail (writeSuccess101d8Trace4 condition).
Definition writeSuccess101d8Trace6 (condition : bool) :=
  subst_trace (Val_Bits writeSuccess101d8NextPc) 4
    (writeSuccessTraceTail (writeSuccess101d8Trace5 condition)).
Definition writeSuccess101d8Trace7 (left : bv 64) (condition : bool) :=
  subst_trace (Val_Bits left) 5
    (writeSuccessTraceTail (writeSuccess101d8Trace6 condition)).
Definition writeSuccess101d8Trace8 (left : bv 64) (condition : bool) :=
  writeSuccessTraceTail (writeSuccess101d8Trace7 left condition).
Definition writeSuccess101d8Trace9 (left right : bv 64) (condition : bool) :=
  subst_trace (Val_Bits right) 6
    (writeSuccessTraceTail (writeSuccess101d8Trace8 left condition)).
Definition writeSuccess101d8Trace10 (left right : bv 64) (condition : bool) :=
  writeSuccessTraceTail (writeSuccess101d8Trace9 left right condition).
Definition writeSuccess101d8Trace11 (left right : bv 64) (condition : bool) :=
  subst_trace (Val_Bool condition) 7
    (writeSuccessTraceTail (writeSuccess101d8Trace10 left right condition)).
Definition writeSuccess101d8Trace12 (left right : bv 64) (condition : bool) :=
  subst_trace (Val_Bits writeSuccess101d8TakenPc) 8
    (writeSuccessTraceTail (writeSuccess101d8Trace11 left right condition)).

Definition writeSuccess101d8Branches (left right : bv 64) (condition : bool) : list isla_trace :=
  match writeSuccess101d8Trace12 left right condition with
  | tcases branches => branches
  | _ => []
  end.
Definition writeSuccess101d8TakenTrace (left right : bv 64) :=
  nth 0 (writeSuccess101d8Branches left right true) tnil.
Definition writeSuccess101d8TakenWrongTrace (left right : bv 64) :=
  nth 1 (writeSuccess101d8Branches left right true) tnil.
Definition writeSuccess101d8FallthroughTrace (left right : bv 64) :=
  nth 1 (writeSuccess101d8Branches left right false) tnil.
Definition writeSuccess101d8FallthroughWrongTrace (left right : bv 64) :=
  nth 0 (writeSuccess101d8Branches left right false) tnil.

Lemma writeSuccess101d8TakenBranchesExact left right :
  writeSuccess101d8Branches left right true =
    [writeSuccess101d8TakenTrace left right;
     writeSuccess101d8TakenWrongTrace left right].
Proof.
  unfold writeSuccess101d8Branches, writeSuccess101d8TakenTrace,
    writeSuccess101d8TakenWrongTrace.
  cbn [writeSuccess101d8Trace12 writeSuccess101d8Trace11
    writeSuccess101d8Trace10 writeSuccess101d8Trace9
    writeSuccess101d8Trace8 writeSuccess101d8Trace7
    writeSuccess101d8Trace6 writeSuccess101d8Trace5
    writeSuccess101d8Trace4 writeSuccess101d8Trace3
    writeSuccess101d8Trace2 writeSuccess101d8Trace1
    writeSuccess101d8NextPc writeSuccess101d8TakenPc
    writeSuccessTraceTail a101d8].
  reflexivity.
Qed.

Lemma writeSuccess101d8FallthroughBranchesExact left right :
  writeSuccess101d8Branches left right false =
    [writeSuccess101d8FallthroughWrongTrace left right;
     writeSuccess101d8FallthroughTrace left right].
Proof.
  unfold writeSuccess101d8Branches, writeSuccess101d8FallthroughTrace,
    writeSuccess101d8FallthroughWrongTrace.
  cbn [writeSuccess101d8Trace12 writeSuccess101d8Trace11
    writeSuccess101d8Trace10 writeSuccess101d8Trace9
    writeSuccess101d8Trace8 writeSuccess101d8Trace7
    writeSuccess101d8Trace6 writeSuccess101d8Trace5
    writeSuccess101d8Trace4 writeSuccess101d8Trace3
    writeSuccess101d8Trace2 writeSuccess101d8Trace1
    writeSuccess101d8NextPc writeSuccess101d8TakenPc
    writeSuccessTraceTail a101d8].
  reflexivity.
Qed.
Definition writeSuccess101d8TakenTrace1 (left right : bv 64) :=
  writeSuccessTraceTail (writeSuccess101d8TakenTrace left right).
Definition writeSuccess101d8TakenBit : bv 1 :=
  bv_extract 0 1 (bv_shiftr writeSuccess101d8TakenPc (BV 64 1)).
Definition writeSuccess101d8TakenTrace2 (left right : bv 64) :=
  subst_trace (Val_Bits writeSuccess101d8TakenBit) 9
    (writeSuccessTraceTail (writeSuccess101d8TakenTrace1 left right)).
Definition writeSuccess101d8TakenTrace3 (left right : bv 64) :=
  writeSuccessTraceTail (writeSuccess101d8TakenTrace2 left right).
Definition writeSuccess101d8TakenTrace4 (left right : bv 64) :=
  writeSuccessTraceTail (writeSuccess101d8TakenTrace3 left right).
Definition writeSuccess101d8FallthroughTrace1 (left right : bv 64) :=
  writeSuccessTraceTail (writeSuccess101d8FallthroughTrace left right).
Definition writeSuccess101d8FallthroughTrace2 (left right : bv 64) :=
  writeSuccessTraceTail (writeSuccess101d8FallthroughTrace1 left right).

Print Assumptions writeSuccess101d8TakenBranchesExact.
Print Assumptions writeSuccess101d8FallthroughBranchesExact.

Definition writeSuccess101d8Before regs global : IslaState :=
  (writeSuccess15694Local a101d8 regs, global).
Definition writeSuccess101d8TakenRegs regs : reg_map :=
  <["PC" := RVal_Bits writeSuccess101d8TakenPc]> regs.
Definition writeSuccess101d8FallthroughRegs regs : reg_map :=
  <["PC" := RVal_Bits writeSuccess101d8NextPc]> regs.
Definition writeSuccess101d8TakenAfter regs global : IslaState :=
  (writeSuccess15694Local a101e0 (writeSuccess101d8TakenRegs regs), global).
Definition writeSuccess101d8FallthroughAfter regs global : IslaState :=
  (writeSuccess15694Local a101dc (writeSuccess101d8FallthroughRegs regs), global).

Lemma writeSuccess101d8PcValues :
  writeSuccess101d8NextPc = Z_to_bv 64 0x101dc /\
  writeSuccess101d8TakenPc = Z_to_bv 64 0x101e0.
Proof. vm_compute. split; apply bv_eq; reflexivity. Qed.

Lemma writeSuccessInstructionPrefixPathAppend before first middle second after :
  IslaInstructionPrefixPath before first middle ->
  IslaInstructionPrefixPath middle second after ->
  IslaInstructionPrefixPath before (first ++ second) after.
Proof.
  intros Hfirst Hsecond. induction Hfirst; cbn; first exact Hsecond.
  econstructor; eauto.
Qed.

Definition writeSuccess101d8CommonLocals (left right : bv 64)
    (condition : bool) regs :=
  [writeSuccess15694Local (writeSuccess101d8Trace1 condition) regs;
   writeSuccess15694Local (writeSuccess101d8Trace2 condition) regs;
   writeSuccess15694Local (writeSuccess101d8Trace3 condition) regs;
   writeSuccess15694Local (writeSuccess101d8Trace4 condition) regs;
   writeSuccess15694Local (writeSuccess101d8Trace5 condition) regs;
   writeSuccess15694Local (writeSuccess101d8Trace6 condition) regs;
   writeSuccess15694Local (writeSuccess101d8Trace7 left condition) regs;
   writeSuccess15694Local (writeSuccess101d8Trace8 left condition) regs;
   writeSuccess15694Local (writeSuccess101d8Trace9 left right condition) regs;
   writeSuccess15694Local (writeSuccess101d8Trace10 left right condition) regs;
   writeSuccess15694Local (writeSuccess101d8Trace11 left right condition) regs;
   writeSuccess15694Local (writeSuccess101d8Trace12 left right condition) regs].
Definition writeSuccess101d8CommonObservations (left right : bv 64)
    (condition : bool) regs global :=
  map (fun local => writeSuccess15694Observation local global)
    (writeSuccess101d8CommonLocals left right condition regs).

Lemma writeSuccess101d8CommonPath regs global (left right : bv 64)
    (condition : bool) :
  regs !! "PC" = Some (RVal_Bits (Z_to_bv 64 0x101d8)) ->
  regs !! "x15" = Some (RVal_Bits left) ->
  regs !! "x12" = Some (RVal_Bits right) ->
  eval_a_exp regs writeSuccess15694Mstatus = Some (Val_Bool true) ->
  eval_exp (writeSuccess101d8Condition left right) = Some (Val_Bool condition) ->
  IslaInstructionPrefixPath (writeSuccess101d8Before regs global)
    (writeSuccess101d8CommonObservations left right condition regs global)
    (writeSuccess15694Local
      (writeSuccess101d8Trace12 left right condition) regs, global).
Proof.
  intros Hpc Hx15 Hx12 Hmstatus Hcondition.
  have Halign := writeSuccess101d8AlignmentHolds regs Hpc.
  unfold writeSuccess101d8CommonObservations, writeSuccess101d8CommonLocals.
  eapply IslaInstructionPrefixStep; first discriminate.
  { apply writeSuccessSeqSilent; first reflexivity.
    unfold writeSuccess101d8Before, writeSuccess15694Local,
      writeSuccess101d8Trace1, writeSuccessTraceTail, a101d8. cbn.
    apply DeclareConstBitVecS' with (b := BV 64 0). }
  eapply IslaInstructionPrefixStep; first discriminate.
  { apply writeSuccessSeqAssume; first reflexivity.
    unfold writeSuccess101d8Trace1, writeSuccessTraceTail, a101d8. cbn.
    eapply AssumeS. exact Hmstatus. }
  eapply IslaInstructionPrefixStep; first discriminate.
  { apply writeSuccessSeqSilent; first reflexivity.
    unfold writeSuccess101d8Trace2, writeSuccess101d8Trace1,
      writeSuccessTraceTail, a101d8. cbn.
    apply DeclareConstBitVecS' with (b := Z_to_bv 64 0x101d8). }
  eapply IslaInstructionPrefixStep; first discriminate.
  { apply writeSuccessSeqAssume; first reflexivity.
    unfold writeSuccess101d8Trace3, writeSuccess101d8Trace2,
      writeSuccess101d8Trace1, writeSuccessTraceTail, a101d8. cbn.
    eapply AssumeS. exact Halign. }
  eapply IslaInstructionPrefixStep; first discriminate.
  { eapply writeSuccessSeqReadReg with
      (root := RVal_Bits (Z_to_bv 64 0x101d8))
      (value := RVal_Bits (Z_to_bv 64 0x101d8)).
    - reflexivity.
    - unfold writeSuccess101d8Trace4, writeSuccess101d8Trace3,
        writeSuccess101d8Trace2, writeSuccess101d8Trace1,
        writeSuccessTraceTail, a101d8. cbn. constructor.
    - exact Hpc.
    - reflexivity.
    - reflexivity. }
  eapply IslaInstructionPrefixStep; first discriminate.
  { apply writeSuccessSeqSilent; first reflexivity.
    unfold writeSuccess101d8Trace5, writeSuccess101d8Trace4,
      writeSuccess101d8Trace3, writeSuccess101d8Trace2,
      writeSuccess101d8Trace1, writeSuccess101d8NextPc,
      writeSuccessTraceTail, a101d8. cbn.
    eapply DefineConstS with (v := Val_Bits writeSuccess101d8NextPc).
    reflexivity. }
  eapply IslaInstructionPrefixStep; first discriminate.
  { apply writeSuccessSeqSilent; first reflexivity.
    cbn [writeSuccess101d8Trace6 writeSuccess101d8Trace5
      writeSuccess101d8Trace4 writeSuccess101d8Trace3
      writeSuccess101d8Trace2 writeSuccess101d8Trace1
      writeSuccess101d8NextPc writeSuccessTraceTail a101d8].
    apply DeclareConstBitVecS' with (b := left). }
  eapply IslaInstructionPrefixStep; first discriminate.
  { eapply writeSuccessSeqReadReg with
      (root := RVal_Bits left) (value := RVal_Bits left).
    - reflexivity.
    - cbn [writeSuccess101d8Trace7 writeSuccess101d8Trace6
        writeSuccess101d8Trace5 writeSuccess101d8Trace4
        writeSuccess101d8Trace3 writeSuccess101d8Trace2
        writeSuccess101d8Trace1 writeSuccess101d8NextPc
        writeSuccessTraceTail a101d8]. constructor.
    - exact Hx15.
    - reflexivity.
    - reflexivity. }
  eapply IslaInstructionPrefixStep; first discriminate.
  { apply writeSuccessSeqSilent; first reflexivity.
    cbn [writeSuccess101d8Trace8 writeSuccess101d8Trace7
      writeSuccess101d8Trace6 writeSuccess101d8Trace5
      writeSuccess101d8Trace4 writeSuccess101d8Trace3
      writeSuccess101d8Trace2 writeSuccess101d8Trace1
      writeSuccess101d8NextPc writeSuccessTraceTail a101d8].
    apply DeclareConstBitVecS' with (b := right). }
  eapply IslaInstructionPrefixStep; first discriminate.
  { eapply writeSuccessSeqReadReg with
      (root := RVal_Bits right) (value := RVal_Bits right).
    - reflexivity.
    - cbn [writeSuccess101d8Trace9 writeSuccess101d8Trace8
        writeSuccess101d8Trace7 writeSuccess101d8Trace6
        writeSuccess101d8Trace5 writeSuccess101d8Trace4
        writeSuccess101d8Trace3 writeSuccess101d8Trace2
        writeSuccess101d8Trace1 writeSuccess101d8NextPc
        writeSuccessTraceTail a101d8]. constructor.
    - exact Hx12.
    - reflexivity.
    - reflexivity. }
  eapply IslaInstructionPrefixStep; first discriminate.
  { apply writeSuccessSeqSilent; first reflexivity.
    cbn [writeSuccess101d8Trace10 writeSuccess101d8Trace9
      writeSuccess101d8Trace8 writeSuccess101d8Trace7
      writeSuccess101d8Trace6 writeSuccess101d8Trace5
      writeSuccess101d8Trace4 writeSuccess101d8Trace3
      writeSuccess101d8Trace2 writeSuccess101d8Trace1
      writeSuccess101d8NextPc writeSuccessTraceTail a101d8].
    eapply DefineConstS with (v := Val_Bool condition). exact Hcondition. }
  eapply IslaInstructionPrefixStep; first discriminate.
  { apply writeSuccessSeqSilent; first reflexivity.
    cbn [writeSuccess101d8Trace11 writeSuccess101d8Trace10
      writeSuccess101d8Trace9 writeSuccess101d8Trace8
      writeSuccess101d8Trace7 writeSuccess101d8Trace6
      writeSuccess101d8Trace5 writeSuccess101d8Trace4
      writeSuccess101d8Trace3 writeSuccess101d8Trace2
      writeSuccess101d8Trace1 writeSuccess101d8NextPc
      writeSuccess101d8TakenPc writeSuccessTraceTail a101d8].
    eapply DefineConstS with (v := Val_Bits writeSuccess101d8TakenPc).
    reflexivity. }
  apply IslaInstructionPrefixRefl.
Qed.

Print Assumptions writeSuccess101d8CommonPath.

Definition writeSuccess101d8TakenLocals left right regs :=
  [writeSuccess15694Local (writeSuccess101d8TakenTrace left right) regs;
   writeSuccess15694Local (writeSuccess101d8TakenTrace1 left right) regs;
   writeSuccess15694Local (writeSuccess101d8TakenTrace2 left right) regs;
   writeSuccess15694Local (writeSuccess101d8TakenTrace3 left right) regs;
   writeSuccess15694Local (writeSuccess101d8TakenTrace4 left right)
     (writeSuccess101d8TakenRegs regs)].
Definition writeSuccess101d8TakenObservations left right regs global :=
  map (fun local => writeSuccess15694Observation local global)
    (writeSuccess101d8TakenLocals left right regs).
Definition writeSuccess101d8FallthroughLocals left right regs :=
  [writeSuccess15694Local (writeSuccess101d8FallthroughTrace left right) regs;
   writeSuccess15694Local (writeSuccess101d8FallthroughTrace1 left right) regs;
   writeSuccess15694Local (writeSuccess101d8FallthroughTrace2 left right)
     (writeSuccess101d8FallthroughRegs regs)].
Definition writeSuccess101d8FallthroughObservations left right regs global :=
  map (fun local => writeSuccess15694Observation local global)
    (writeSuccess101d8FallthroughLocals left right regs).

Lemma writeSuccess101d8TakenSuffixPath regs global (left right : bv 64) :
  regs !! "PC" = Some (RVal_Bits (Z_to_bv 64 0x101d8)) ->
  IslaInstructionPrefixPath
    (writeSuccess15694Local (writeSuccess101d8Trace12 left right true) regs,
      global)
    (writeSuccess101d8TakenObservations left right regs global)
    (writeSuccess15694Local tnil (writeSuccess101d8TakenRegs regs), global).
Proof.
  intros Hpc. unfold writeSuccess101d8TakenObservations,
    writeSuccess101d8TakenLocals.
  eapply IslaInstructionPrefixStep; first discriminate.
  { apply writeSuccessSeqSilent; first reflexivity.
    cbn [writeSuccess101d8Trace12 writeSuccess101d8Trace11
      writeSuccess101d8Trace10 writeSuccess101d8Trace9
      writeSuccess101d8Trace8 writeSuccess101d8Trace7
      writeSuccess101d8Trace6 writeSuccess101d8Trace5
      writeSuccess101d8Trace4 writeSuccess101d8Trace3
      writeSuccess101d8Trace2 writeSuccess101d8Trace1
      writeSuccess101d8TakenTrace writeSuccess101d8Branches
      writeSuccess101d8NextPc writeSuccess101d8TakenPc
      writeSuccessTraceTail a101d8].
    eapply CasesES with (es := writeSuccess101d8TakenTrace left right).
    cbn. rewrite elem_of_cons. left. reflexivity. }
  eapply IslaInstructionPrefixStep; first discriminate.
  { apply writeSuccessSeqAssertTrue; first reflexivity.
    cbn [writeSuccess101d8TakenTrace writeSuccess101d8Branches
      writeSuccess101d8Trace12 writeSuccess101d8Trace11
      writeSuccess101d8Trace10 writeSuccess101d8Trace9
      writeSuccess101d8Trace8 writeSuccess101d8Trace7
      writeSuccess101d8Trace6 writeSuccess101d8Trace5
      writeSuccess101d8Trace4 writeSuccess101d8Trace3
      writeSuccess101d8Trace2 writeSuccess101d8Trace1
      writeSuccess101d8NextPc writeSuccess101d8TakenPc
      writeSuccessTraceTail a101d8]. eapply AssertS. reflexivity. }
  eapply IslaInstructionPrefixStep; first discriminate.
  { apply writeSuccessSeqSilent; first reflexivity.
    cbn [writeSuccess101d8TakenTrace1 writeSuccess101d8TakenTrace
      writeSuccess101d8Branches writeSuccess101d8Trace12
      writeSuccess101d8Trace11 writeSuccess101d8Trace10
      writeSuccess101d8Trace9 writeSuccess101d8Trace8
      writeSuccess101d8Trace7 writeSuccess101d8Trace6
      writeSuccess101d8Trace5 writeSuccess101d8Trace4
      writeSuccess101d8Trace3 writeSuccess101d8Trace2
      writeSuccess101d8Trace1 writeSuccess101d8NextPc
      writeSuccess101d8TakenPc writeSuccess101d8TakenBit
      writeSuccessTraceTail a101d8].
    eapply DefineConstS with (v := Val_Bits writeSuccess101d8TakenBit).
    reflexivity. }
  eapply IslaInstructionPrefixStep; first discriminate.
  { apply writeSuccessSeqBranchAddress with
      (target := RVal_Bits writeSuccess101d8TakenPc); first reflexivity.
    cbn [writeSuccess101d8TakenTrace2 writeSuccess101d8TakenTrace1
      writeSuccess101d8TakenTrace writeSuccess101d8Branches
      writeSuccess101d8Trace12 writeSuccess101d8Trace11
      writeSuccess101d8Trace10 writeSuccess101d8Trace9
      writeSuccess101d8Trace8 writeSuccess101d8Trace7
      writeSuccess101d8Trace6 writeSuccess101d8Trace5
      writeSuccess101d8Trace4 writeSuccess101d8Trace3
      writeSuccess101d8Trace2 writeSuccess101d8Trace1
      writeSuccess101d8NextPc writeSuccess101d8TakenPc
      writeSuccess101d8TakenBit writeSuccessTraceTail a101d8]. constructor. }
  eapply IslaInstructionPrefixStep; first discriminate.
  { eapply writeSuccessSeqWriteReg with
      (root := RVal_Bits (Z_to_bv 64 0x101d8))
      (value := RVal_Bits writeSuccess101d8TakenPc)
      (updated := RVal_Bits writeSuccess101d8TakenPc).
    - reflexivity.
    - cbn [writeSuccess101d8TakenTrace3 writeSuccess101d8TakenTrace2
        writeSuccess101d8TakenTrace1 writeSuccess101d8TakenTrace
        writeSuccess101d8Branches writeSuccess101d8Trace12
        writeSuccess101d8Trace11 writeSuccess101d8Trace10
        writeSuccess101d8Trace9 writeSuccess101d8Trace8
        writeSuccess101d8Trace7 writeSuccess101d8Trace6
        writeSuccess101d8Trace5 writeSuccess101d8Trace4
        writeSuccess101d8Trace3 writeSuccess101d8Trace2
        writeSuccess101d8Trace1 writeSuccess101d8NextPc
        writeSuccess101d8TakenPc writeSuccess101d8TakenBit
        writeSuccessTraceTail a101d8]. constructor.
    - exact Hpc.
    - reflexivity.
    - reflexivity. }
  apply IslaInstructionPrefixRefl.
Qed.

Lemma writeSuccess101d8FallthroughSuffixPath regs global (left right : bv 64) :
  regs !! "PC" = Some (RVal_Bits (Z_to_bv 64 0x101d8)) ->
  IslaInstructionPrefixPath
    (writeSuccess15694Local (writeSuccess101d8Trace12 left right false) regs,
      global)
    (writeSuccess101d8FallthroughObservations left right regs global)
    (writeSuccess15694Local tnil
      (writeSuccess101d8FallthroughRegs regs), global).
Proof.
  intros Hpc. unfold writeSuccess101d8FallthroughObservations,
    writeSuccess101d8FallthroughLocals.
  eapply IslaInstructionPrefixStep; first discriminate.
  { apply writeSuccessSeqSilent; first reflexivity.
    cbn [writeSuccess101d8Trace12 writeSuccess101d8Trace11
      writeSuccess101d8Trace10 writeSuccess101d8Trace9
      writeSuccess101d8Trace8 writeSuccess101d8Trace7
      writeSuccess101d8Trace6 writeSuccess101d8Trace5
      writeSuccess101d8Trace4 writeSuccess101d8Trace3
      writeSuccess101d8Trace2 writeSuccess101d8Trace1
      writeSuccess101d8FallthroughTrace writeSuccess101d8Branches
      writeSuccess101d8NextPc writeSuccess101d8TakenPc
      writeSuccessTraceTail a101d8].
    eapply CasesES with (es := writeSuccess101d8FallthroughTrace left right).
    cbn. rewrite elem_of_cons. right. rewrite elem_of_cons. left. reflexivity. }
  eapply IslaInstructionPrefixStep; first discriminate.
  { apply writeSuccessSeqAssertTrue; first reflexivity.
    cbn [writeSuccess101d8FallthroughTrace writeSuccess101d8Branches
      writeSuccess101d8Trace12 writeSuccess101d8Trace11
      writeSuccess101d8Trace10 writeSuccess101d8Trace9
      writeSuccess101d8Trace8 writeSuccess101d8Trace7
      writeSuccess101d8Trace6 writeSuccess101d8Trace5
      writeSuccess101d8Trace4 writeSuccess101d8Trace3
      writeSuccess101d8Trace2 writeSuccess101d8Trace1
      writeSuccess101d8NextPc writeSuccess101d8TakenPc
      writeSuccessTraceTail a101d8]. eapply AssertS. reflexivity. }
  eapply IslaInstructionPrefixStep; first discriminate.
  { eapply writeSuccessSeqWriteReg with
      (root := RVal_Bits (Z_to_bv 64 0x101d8))
      (value := RVal_Bits writeSuccess101d8NextPc)
      (updated := RVal_Bits writeSuccess101d8NextPc).
    - reflexivity.
    - cbn [writeSuccess101d8FallthroughTrace1
        writeSuccess101d8FallthroughTrace writeSuccess101d8Branches
        writeSuccess101d8Trace12 writeSuccess101d8Trace11
        writeSuccess101d8Trace10 writeSuccess101d8Trace9
        writeSuccess101d8Trace8 writeSuccess101d8Trace7
        writeSuccess101d8Trace6 writeSuccess101d8Trace5
        writeSuccess101d8Trace4 writeSuccess101d8Trace3
        writeSuccess101d8Trace2 writeSuccess101d8Trace1
        writeSuccess101d8NextPc writeSuccess101d8TakenPc
        writeSuccessTraceTail a101d8]. constructor.
    - exact Hpc.
    - reflexivity.
    - reflexivity. }
  apply IslaInstructionPrefixRefl.
Qed.

Print Assumptions writeSuccess101d8TakenSuffixPath.
Print Assumptions writeSuccess101d8FallthroughSuffixPath.

Definition writeSuccess101d8TakenAllObservations left right regs global :=
  writeSuccess101d8CommonObservations left right true regs global ++
  writeSuccess101d8TakenObservations left right regs global ++
  [writeSuccess15694Observation
    (writeSuccess101d8TakenAfter regs global).1 global].
Definition writeSuccess101d8FallthroughAllObservations left right regs global :=
  writeSuccess101d8CommonObservations left right false regs global ++
  writeSuccess101d8FallthroughObservations left right regs global ++
  [writeSuccess15694Observation
    (writeSuccess101d8FallthroughAfter regs global).1 global].

Lemma segment_101d8_taken_mstatus regs global (left right : bv 64) :
  regs !! "PC" = Some (RVal_Bits (Z_to_bv 64 0x101d8)) ->
  regs !! "x15" = Some (RVal_Bits left) ->
  regs !! "x12" = Some (RVal_Bits right) ->
  left <> right ->
  global.(seq_instrs) !! Z_to_bv 64 0x101d8 = Some a101d8 ->
  global.(seq_instrs) !! Z_to_bv 64 0x101e0 = Some a101e0 ->
  eval_a_exp regs writeSuccess15694Mstatus = Some (Val_Bool true) ->
  IslaInstructionSegment (writeSuccess101d8Before regs global)
    (writeSuccess101d8TakenAllObservations left right regs global)
    (writeSuccess101d8TakenAfter regs global).
Proof.
  intros Hpc Hx15 Hx12 Hne Hcode Hnext Hmstatus.
  unfold writeSuccess101d8TakenAllObservations.
  eapply islaInstructionSegmentIntro with
    (prefix := writeSuccess101d8CommonObservations left right true regs global ++
      writeSuccess101d8TakenObservations left right regs global)
    (done := (writeSuccess15694Local tnil
      (writeSuccess101d8TakenRegs regs), global))
    (labels := []) (spawned := []).
  - split; first reflexivity. exists (Z_to_bv 64 0x101d8), a101d8.
    cbn. rewrite Hpc Hcode. repeat split; reflexivity.
  - eapply writeSuccessInstructionPrefixPathAppend.
    + eapply writeSuccess101d8CommonPath; eauto.
      apply writeSuccess101d8ConditionTaken. exact Hne.
    + apply writeSuccess101d8TakenSuffixPath. exact Hpc.
  - reflexivity.
  - apply writeSuccessSeqDoneTabled with (next := a101e0) (trace := a101e0).
    + reflexivity. + reflexivity. + constructor.
    + exists (Z_to_bv 64 0x101e0). unfold writeSuccess101d8TakenRegs.
      rewrite lookup_insert. destruct writeSuccess101d8PcValues as (_ & ->).
      rewrite Hnext. repeat split; reflexivity.
  - left. split; first reflexivity. exists (Z_to_bv 64 0x101e0), a101e0.
    cbn. unfold writeSuccess101d8TakenRegs. rewrite lookup_insert.
    destruct writeSuccess101d8PcValues as (_ & ->).
    rewrite Hnext. repeat split; reflexivity.
Qed.

Lemma segment_101d8_fallthrough_mstatus regs global (left right : bv 64) :
  regs !! "PC" = Some (RVal_Bits (Z_to_bv 64 0x101d8)) ->
  regs !! "x15" = Some (RVal_Bits left) ->
  regs !! "x12" = Some (RVal_Bits right) ->
  left = right ->
  global.(seq_instrs) !! Z_to_bv 64 0x101d8 = Some a101d8 ->
  global.(seq_instrs) !! Z_to_bv 64 0x101dc = Some a101dc ->
  eval_a_exp regs writeSuccess15694Mstatus = Some (Val_Bool true) ->
  IslaInstructionSegment (writeSuccess101d8Before regs global)
    (writeSuccess101d8FallthroughAllObservations left right regs global)
    (writeSuccess101d8FallthroughAfter regs global).
Proof.
  intros Hpc Hx15 Hx12 Heq Hcode Hnext Hmstatus.
  unfold writeSuccess101d8FallthroughAllObservations.
  eapply islaInstructionSegmentIntro with
    (prefix := writeSuccess101d8CommonObservations left right false regs global ++
      writeSuccess101d8FallthroughObservations left right regs global)
    (done := (writeSuccess15694Local tnil
      (writeSuccess101d8FallthroughRegs regs), global))
    (labels := []) (spawned := []).
  - split; first reflexivity. exists (Z_to_bv 64 0x101d8), a101d8.
    cbn. rewrite Hpc Hcode. repeat split; reflexivity.
  - eapply writeSuccessInstructionPrefixPathAppend.
    + eapply writeSuccess101d8CommonPath; eauto.
      apply writeSuccess101d8ConditionFallthrough. exact Heq.
    + apply writeSuccess101d8FallthroughSuffixPath. exact Hpc.
  - reflexivity.
  - apply writeSuccessSeqDoneTabled with (next := a101dc) (trace := a101dc).
    + reflexivity. + reflexivity. + constructor.
    + exists (Z_to_bv 64 0x101dc). unfold writeSuccess101d8FallthroughRegs.
      rewrite lookup_insert. destruct writeSuccess101d8PcValues as (-> & _).
      rewrite Hnext. repeat split; reflexivity.
  - left. split; first reflexivity. exists (Z_to_bv 64 0x101dc), a101dc.
    cbn. unfold writeSuccess101d8FallthroughRegs. rewrite lookup_insert.
    destruct writeSuccess101d8PcValues as (-> & _).
    rewrite Hnext. repeat split; reflexivity.
Qed.

Print Assumptions segment_101d8_taken_mstatus.
Print Assumptions segment_101d8_fallthrough_mstatus.

Definition writeSuccess101d8After (left right : bv 64) regs global : IslaState :=
  if decide (left = right)
  then writeSuccess101d8FallthroughAfter regs global
  else writeSuccess101d8TakenAfter regs global.
Definition writeSuccess101d8Observations (left right : bv 64) regs global :=
  if decide (left = right)
  then writeSuccess101d8FallthroughAllObservations left right regs global
  else writeSuccess101d8TakenAllObservations left right regs global.

Lemma segment_101d8_mstatus regs global (left right : bv 64) :
  regs !! "PC" = Some (RVal_Bits (Z_to_bv 64 0x101d8)) ->
  regs !! "x15" = Some (RVal_Bits left) ->
  regs !! "x12" = Some (RVal_Bits right) ->
  global.(seq_instrs) !! Z_to_bv 64 0x101d8 = Some a101d8 ->
  global.(seq_instrs) !! Z_to_bv 64 0x101dc = Some a101dc ->
  global.(seq_instrs) !! Z_to_bv 64 0x101e0 = Some a101e0 ->
  eval_a_exp regs writeSuccess15694Mstatus = Some (Val_Bool true) ->
  IslaInstructionSegment (writeSuccess101d8Before regs global)
    (writeSuccess101d8Observations left right regs global)
    (writeSuccess101d8After left right regs global).
Proof.
  intros Hpc Hx15 Hx12 Hcode Hfall Htaken Hmstatus.
  unfold writeSuccess101d8Observations, writeSuccess101d8After.
  destruct (decide (left = right)) as [Heq|Hne].
  - eapply segment_101d8_fallthrough_mstatus; eauto.
  - eapply segment_101d8_taken_mstatus; eauto.
Qed.

Lemma segment_101d8 regs global (left right : bv 64) :
  regs !! "PC" = Some (RVal_Bits (Z_to_bv 64 0x101d8)) ->
  regs !! "x15" = Some (RVal_Bits left) ->
  regs !! "x12" = Some (RVal_Bits right) ->
  global.(seq_instrs) !! Z_to_bv 64 0x101d8 = Some a101d8 ->
  global.(seq_instrs) !! Z_to_bv 64 0x101dc = Some a101dc ->
  global.(seq_instrs) !! Z_to_bv 64 0x101e0 = Some a101e0 ->
  writeSuccessTraceAssumptions (writeSuccess101d8Before regs global) ->
  IslaInstructionSegment (writeSuccess101d8Before regs global)
    (writeSuccess101d8Observations left right regs global)
    (writeSuccess101d8After left right regs global).
Proof.
  intros Hpc Hx15 Hx12 Hcode Hfall Htaken Hassumptions.
  eapply segment_101d8_mstatus; eauto.
  exact (writeSuccess15694MstatusFromTraceAssumptions regs global Hassumptions).
Qed.

Definition writeSuccess101d8FinalRegs (left right : bv 64) regs : reg_map :=
  if decide (left = right)
  then writeSuccess101d8FallthroughRegs regs
  else writeSuccess101d8TakenRegs regs.

Lemma writeSuccess101d8AfterRegs left right regs global :
  (writeSuccess101d8After left right regs global).1.(seq_regs) =
  writeSuccess101d8FinalRegs left right regs.
Proof. unfold writeSuccess101d8After, writeSuccess101d8FinalRegs.
  destruct decide; reflexivity. Qed.

Lemma writeSuccess101d8RegsLookupOther regs (left right : bv 64) reg :
  reg <> "PC" ->
  writeSuccess101d8FinalRegs left right regs !! reg = regs !! reg.
Proof.
  intros Hreg. unfold writeSuccess101d8FinalRegs,
    writeSuccess101d8TakenRegs, writeSuccess101d8FallthroughRegs,
    writeSuccess15694Local. destruct decide.
  - rewrite lookup_insert_ne; last naive_solver. reflexivity.
  - rewrite lookup_insert_ne; last naive_solver. reflexivity.
Qed.

Lemma writeSuccess101d8RegsDom regs (left right : bv 64) :
  regs !! "PC" = Some (RVal_Bits (Z_to_bv 64 0x101d8)) ->
  dom (writeSuccess101d8FinalRegs left right regs) = dom regs.
Proof.
  intros Hpc. apply elem_of_dom_2 in Hpc.
  unfold writeSuccess101d8FinalRegs, writeSuccess101d8TakenRegs,
    writeSuccess101d8FallthroughRegs.
  destruct decide; rewrite dom_insert_L; set_solver.
Qed.

Print Assumptions segment_101d8_mstatus.
Print Assumptions segment_101d8.
Print Assumptions writeSuccess101d8RegsDom.
