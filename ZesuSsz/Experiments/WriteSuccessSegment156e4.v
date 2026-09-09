(* Generated from the pinned bnez trace shape. *)
(* The renderer validates the pinned operands and endpoints. *)
From Coq Require Import Eqdep_dec Lists.List ZArith.ZArith.
Require Import isla.riscv64.riscv64.
Require Import IslaTraces.write_success_95.a156e4.
Require Import IslaTraces.write_success_96.a156e8.
Require Import IslaTraces.write_success_90.a15694.
Require Import ZesuSsz.Contracts.InstructionBoundary.
Require Import ZesuSsz.Experiments.WriteSuccessSegmentAutomation.
Require Import ZesuSsz.Experiments.WriteSuccessCoverageAutomation.
Require Import ZesuSsz.Experiments.WriteSuccessSegment15694.

Import ListNotations.
Open Scope Z_scope.

Definition writeSuccess156e4Alignment : a_exp :=
  AExp_Binop Eq
    (AExp_Unop (Extract 1 0) (AExp_Val (AVal_Var "PC" []) Mk_annot) Mk_annot)
    (AExp_Val (AVal_Bits (BV 2 0)) Mk_annot) Mk_annot.

Definition writeSuccess156e4Condition (value : bv 64) : exp :=
  Unop Not
    (Binop Eq (Val (Val_Bits value) Mk_annot)
      (Val (Val_Bits (BV 64 0)) Mk_annot) Mk_annot) Mk_annot.

Lemma writeSuccessBvnToBvSame n (value : bv n) :
  bvn_to_bv n (bv_to_bvn value) = Some value.
Proof.
  destruct value as [bits Hbits]. unfold bvn_to_bv. cbn.
  destruct (decide (n = n)) as [Heq|Hneq].
  - f_equal. symmetry. apply Eqdep_dec.eq_rect_eq_dec. apply N.eq_dec.
  - exfalso. apply Hneq. reflexivity.
Qed.

Local Opaque bvn_to_bv.

Lemma writeSuccess156e4AlignmentHolds regs :
  regs !! "PC" = Some (RVal_Bits (Z_to_bv 64 0x156e4)) ->
  eval_a_exp regs writeSuccess156e4Alignment = Some (Val_Bool true).
Proof.
  intros Hpc. unfold writeSuccess156e4Alignment. cbn. rewrite Hpc. vm_compute.
  reflexivity.
Qed.

Lemma writeSuccess156e4ConditionTaken value :
  value <> (BV 64 0) ->
  eval_exp (writeSuccess156e4Condition value) = Some (Val_Bool true).
Proof.
  intros Hne. unfold writeSuccess156e4Condition. cbn.
  rewrite writeSuccessBvnToBvSame. cbn.
  case_bool_decide; first contradiction. reflexivity.
Qed.

Lemma writeSuccess156e4ConditionFallthrough value :
  value = (BV 64 0) ->
  eval_exp (writeSuccess156e4Condition value) = Some (Val_Bool false).
Proof.
  intros ->. unfold writeSuccess156e4Condition. cbn.
  rewrite writeSuccessBvnToBvSame. cbn.
  case_bool_decide; last contradiction. reflexivity.
Qed.

Print Assumptions writeSuccess156e4AlignmentHolds.
Print Assumptions writeSuccess156e4ConditionTaken.
Print Assumptions writeSuccess156e4ConditionFallthrough.

Definition writeSuccess156e4NextPc : bv 64 :=
  (Z_to_bv 64 0x156e4 + BV 64 4)%bv.
Definition writeSuccess156e4TakenPc : bv 64 :=
  (Z_to_bv 64 0x156e4 + BV 64 0xffffffffffffffb0)%bv.

Definition writeSuccess156e4Trace1 (condition : bool) :=
  subst_trace (Val_Bits (BV 64 0)) 2 (writeSuccessTraceTail a156e4).
Definition writeSuccess156e4Trace2 (condition : bool) :=
  writeSuccessTraceTail (writeSuccess156e4Trace1 condition).
Definition writeSuccess156e4Trace3 (condition : bool) :=
  subst_trace (Val_Bits (Z_to_bv 64 0x156e4)) 3
    (writeSuccessTraceTail (writeSuccess156e4Trace2 condition)).
Definition writeSuccess156e4Trace4 (condition : bool) :=
  writeSuccessTraceTail (writeSuccess156e4Trace3 condition).
Definition writeSuccess156e4Trace5 (condition : bool) :=
  writeSuccessTraceTail (writeSuccess156e4Trace4 condition).
Definition writeSuccess156e4Trace6 (condition : bool) :=
  subst_trace (Val_Bits writeSuccess156e4NextPc) 4
    (writeSuccessTraceTail (writeSuccess156e4Trace5 condition)).
Definition writeSuccess156e4Trace7 (value : bv 64) (condition : bool) :=
  subst_trace (Val_Bits value) 5
    (writeSuccessTraceTail (writeSuccess156e4Trace6 condition)).
Definition writeSuccess156e4Trace8 (value : bv 64) (condition : bool) :=
  writeSuccessTraceTail (writeSuccess156e4Trace7 value condition).
Definition writeSuccess156e4Trace9 (value : bv 64) (condition : bool) :=
  subst_trace (Val_Bool condition) 6
    (writeSuccessTraceTail (writeSuccess156e4Trace8 value condition)).
Definition writeSuccess156e4Trace10 (value : bv 64) (condition : bool) :=
  subst_trace (Val_Bits writeSuccess156e4TakenPc) 7
    (writeSuccessTraceTail (writeSuccess156e4Trace9 value condition)).

Definition writeSuccess156e4Branches (value : bv 64) (condition : bool) : list isla_trace :=
  match writeSuccess156e4Trace10 value condition with
  | tcases branches => branches
  | _ => []
  end.
Definition writeSuccess156e4TakenTrace (value : bv 64) :=
  nth 0 (writeSuccess156e4Branches value true) tnil.
Definition writeSuccess156e4TakenWrongTrace (value : bv 64) :=
  nth 1 (writeSuccess156e4Branches value true) tnil.
Definition writeSuccess156e4FallthroughTrace (value : bv 64) :=
  nth 1 (writeSuccess156e4Branches value false) tnil.
Definition writeSuccess156e4FallthroughWrongTrace (value : bv 64) :=
  nth 0 (writeSuccess156e4Branches value false) tnil.

Lemma writeSuccess156e4TakenBranchesExact value :
  writeSuccess156e4Branches value true =
    [writeSuccess156e4TakenTrace value;
     writeSuccess156e4TakenWrongTrace value].
Proof.
  unfold writeSuccess156e4Branches, writeSuccess156e4TakenTrace,
    writeSuccess156e4TakenWrongTrace.
  cbn [writeSuccess156e4Trace10 writeSuccess156e4Trace9
    writeSuccess156e4Trace8 writeSuccess156e4Trace7
    writeSuccess156e4Trace6 writeSuccess156e4Trace5
    writeSuccess156e4Trace4 writeSuccess156e4Trace3
    writeSuccess156e4Trace2 writeSuccess156e4Trace1
    writeSuccess156e4NextPc writeSuccess156e4TakenPc
    writeSuccessTraceTail a156e4].
  reflexivity.
Qed.

Lemma writeSuccess156e4FallthroughBranchesExact value :
  writeSuccess156e4Branches value false =
    [writeSuccess156e4FallthroughWrongTrace value;
     writeSuccess156e4FallthroughTrace value].
Proof.
  unfold writeSuccess156e4Branches, writeSuccess156e4FallthroughTrace,
    writeSuccess156e4FallthroughWrongTrace.
  cbn [writeSuccess156e4Trace10 writeSuccess156e4Trace9
    writeSuccess156e4Trace8 writeSuccess156e4Trace7
    writeSuccess156e4Trace6 writeSuccess156e4Trace5
    writeSuccess156e4Trace4 writeSuccess156e4Trace3
    writeSuccess156e4Trace2 writeSuccess156e4Trace1
    writeSuccess156e4NextPc writeSuccess156e4TakenPc
    writeSuccessTraceTail a156e4].
  reflexivity.
Qed.
Definition writeSuccess156e4TakenTrace1 (value : bv 64) :=
  writeSuccessTraceTail (writeSuccess156e4TakenTrace value).
Definition writeSuccess156e4TakenBit : bv 1 :=
  bv_extract 0 1 (bv_shiftr writeSuccess156e4TakenPc (BV 64 1)).
Definition writeSuccess156e4TakenTrace2 (value : bv 64) :=
  subst_trace (Val_Bits writeSuccess156e4TakenBit) 9
    (writeSuccessTraceTail (writeSuccess156e4TakenTrace1 value)).
Definition writeSuccess156e4TakenTrace3 (value : bv 64) :=
  writeSuccessTraceTail (writeSuccess156e4TakenTrace2 value).
Definition writeSuccess156e4TakenTrace4 (value : bv 64) :=
  writeSuccessTraceTail (writeSuccess156e4TakenTrace3 value).
Definition writeSuccess156e4FallthroughTrace1 (value : bv 64) :=
  writeSuccessTraceTail (writeSuccess156e4FallthroughTrace value).
Definition writeSuccess156e4FallthroughTrace2 (value : bv 64) :=
  writeSuccessTraceTail (writeSuccess156e4FallthroughTrace1 value).

Print Assumptions writeSuccess156e4TakenBranchesExact.
Print Assumptions writeSuccess156e4FallthroughBranchesExact.

Definition writeSuccess156e4Before regs global : IslaState :=
  (writeSuccess15694Local a156e4 regs, global).
Definition writeSuccess156e4TakenRegs regs : reg_map :=
  <["PC" := RVal_Bits writeSuccess156e4TakenPc]> regs.
Definition writeSuccess156e4FallthroughRegs regs : reg_map :=
  <["PC" := RVal_Bits writeSuccess156e4NextPc]> regs.
Definition writeSuccess156e4TakenAfter regs global : IslaState :=
  (writeSuccess15694Local a15694 (writeSuccess156e4TakenRegs regs), global).
Definition writeSuccess156e4FallthroughAfter regs global : IslaState :=
  (writeSuccess15694Local a156e8 (writeSuccess156e4FallthroughRegs regs), global).

Lemma writeSuccess156e4PcValues :
  writeSuccess156e4NextPc = Z_to_bv 64 0x156e8 /\
  writeSuccess156e4TakenPc = Z_to_bv 64 0x15694.
Proof. vm_compute. split; apply bv_eq; reflexivity. Qed.

Lemma writeSuccessInstructionPrefixPathAppend before first middle second after :
  IslaInstructionPrefixPath before first middle ->
  IslaInstructionPrefixPath middle second after ->
  IslaInstructionPrefixPath before (first ++ second) after.
Proof.
  intros Hfirst Hsecond. induction Hfirst; cbn; first exact Hsecond.
  econstructor; eauto.
Qed.

Definition writeSuccess156e4CommonLocals (value : bv 64)
    (condition : bool) regs :=
  [writeSuccess15694Local (writeSuccess156e4Trace1 condition) regs;
   writeSuccess15694Local (writeSuccess156e4Trace2 condition) regs;
   writeSuccess15694Local (writeSuccess156e4Trace3 condition) regs;
   writeSuccess15694Local (writeSuccess156e4Trace4 condition) regs;
   writeSuccess15694Local (writeSuccess156e4Trace5 condition) regs;
   writeSuccess15694Local (writeSuccess156e4Trace6 condition) regs;
   writeSuccess15694Local (writeSuccess156e4Trace7 value condition) regs;
   writeSuccess15694Local (writeSuccess156e4Trace8 value condition) regs;
   writeSuccess15694Local (writeSuccess156e4Trace9 value condition) regs;
   writeSuccess15694Local (writeSuccess156e4Trace10 value condition) regs].
Definition writeSuccess156e4CommonObservations (value : bv 64)
    (condition : bool) regs global :=
  map (fun local => writeSuccess15694Observation local global)
    (writeSuccess156e4CommonLocals value condition regs).

Lemma writeSuccess156e4CommonPath regs global (value : bv 64)
    (condition : bool) :
  regs !! "PC" = Some (RVal_Bits (Z_to_bv 64 0x156e4)) ->
  regs !! "x9" = Some (RVal_Bits value) ->
  eval_a_exp regs writeSuccess15694Mstatus = Some (Val_Bool true) ->
  eval_exp (writeSuccess156e4Condition value) = Some (Val_Bool condition) ->
  IslaInstructionPrefixPath (writeSuccess156e4Before regs global)
    (writeSuccess156e4CommonObservations value condition regs global)
    (writeSuccess15694Local
      (writeSuccess156e4Trace10 value condition) regs, global).
Proof.
  intros Hpc Hx9 Hmstatus Hcondition.
  have Halign := writeSuccess156e4AlignmentHolds regs Hpc.
  unfold writeSuccess156e4CommonObservations, writeSuccess156e4CommonLocals.
  eapply IslaInstructionPrefixStep; first discriminate.
  { apply writeSuccessSeqSilent; first reflexivity.
    unfold writeSuccess156e4Before, writeSuccess15694Local,
      writeSuccess156e4Trace1, writeSuccessTraceTail, a156e4. cbn.
    apply DeclareConstBitVecS' with (b := BV 64 0). }
  eapply IslaInstructionPrefixStep; first discriminate.
  { apply writeSuccessSeqAssume; first reflexivity.
    unfold writeSuccess156e4Trace1, writeSuccessTraceTail, a156e4. cbn.
    eapply AssumeS. exact Hmstatus. }
  eapply IslaInstructionPrefixStep; first discriminate.
  { apply writeSuccessSeqSilent; first reflexivity.
    unfold writeSuccess156e4Trace2, writeSuccess156e4Trace1,
      writeSuccessTraceTail, a156e4. cbn.
    apply DeclareConstBitVecS' with (b := Z_to_bv 64 0x156e4). }
  eapply IslaInstructionPrefixStep; first discriminate.
  { apply writeSuccessSeqAssume; first reflexivity.
    unfold writeSuccess156e4Trace3, writeSuccess156e4Trace2,
      writeSuccess156e4Trace1, writeSuccessTraceTail, a156e4. cbn.
    eapply AssumeS. exact Halign. }
  eapply IslaInstructionPrefixStep; first discriminate.
  { eapply writeSuccessSeqReadReg with
      (root := RVal_Bits (Z_to_bv 64 0x156e4))
      (value := RVal_Bits (Z_to_bv 64 0x156e4)).
    - reflexivity.
    - unfold writeSuccess156e4Trace4, writeSuccess156e4Trace3,
        writeSuccess156e4Trace2, writeSuccess156e4Trace1,
        writeSuccessTraceTail, a156e4. cbn. constructor.
    - exact Hpc.
    - reflexivity.
    - reflexivity. }
  eapply IslaInstructionPrefixStep; first discriminate.
  { apply writeSuccessSeqSilent; first reflexivity.
    unfold writeSuccess156e4Trace5, writeSuccess156e4Trace4,
      writeSuccess156e4Trace3, writeSuccess156e4Trace2,
      writeSuccess156e4Trace1, writeSuccess156e4NextPc,
      writeSuccessTraceTail, a156e4. cbn.
    eapply DefineConstS with (v := Val_Bits writeSuccess156e4NextPc).
    reflexivity. }
  eapply IslaInstructionPrefixStep; first discriminate.
  { apply writeSuccessSeqSilent; first reflexivity.
    cbn [writeSuccess156e4Trace6 writeSuccess156e4Trace5
      writeSuccess156e4Trace4 writeSuccess156e4Trace3
      writeSuccess156e4Trace2 writeSuccess156e4Trace1
      writeSuccess156e4NextPc writeSuccessTraceTail a156e4].
    apply DeclareConstBitVecS' with (b := value). }
  eapply IslaInstructionPrefixStep; first discriminate.
  { eapply writeSuccessSeqReadReg with
      (root := RVal_Bits value) (value := RVal_Bits value).
    - reflexivity.
    - cbn [writeSuccess156e4Trace7 writeSuccess156e4Trace6
        writeSuccess156e4Trace5 writeSuccess156e4Trace4
        writeSuccess156e4Trace3 writeSuccess156e4Trace2
        writeSuccess156e4Trace1 writeSuccess156e4NextPc
        writeSuccessTraceTail a156e4]. constructor.
    - exact Hx9.
    - reflexivity.
    - reflexivity. }
  eapply IslaInstructionPrefixStep; first discriminate.
  { apply writeSuccessSeqSilent; first reflexivity.
    cbn [writeSuccess156e4Trace8 writeSuccess156e4Trace7
      writeSuccess156e4Trace8 writeSuccess156e4Trace7
      writeSuccess156e4Trace6 writeSuccess156e4Trace5
      writeSuccess156e4Trace4 writeSuccess156e4Trace3
      writeSuccess156e4Trace2 writeSuccess156e4Trace1
      writeSuccess156e4NextPc writeSuccessTraceTail a156e4].
    eapply DefineConstS with (v := Val_Bool condition). exact Hcondition. }
  eapply IslaInstructionPrefixStep; first discriminate.
  { apply writeSuccessSeqSilent; first reflexivity.
    cbn [writeSuccess156e4Trace9 writeSuccess156e4Trace8
      writeSuccess156e4Trace7 writeSuccess156e4Trace6
      writeSuccess156e4Trace5 writeSuccess156e4Trace4
      writeSuccess156e4Trace3 writeSuccess156e4Trace2
      writeSuccess156e4Trace1 writeSuccess156e4NextPc
      writeSuccess156e4TakenPc writeSuccessTraceTail a156e4].
    eapply DefineConstS with (v := Val_Bits writeSuccess156e4TakenPc).
    reflexivity. }
  apply IslaInstructionPrefixRefl.
Qed.

Print Assumptions writeSuccess156e4CommonPath.

Definition writeSuccess156e4TakenLocals value regs :=
  [writeSuccess15694Local (writeSuccess156e4TakenTrace value) regs;
   writeSuccess15694Local (writeSuccess156e4TakenTrace1 value) regs;
   writeSuccess15694Local (writeSuccess156e4TakenTrace2 value) regs;
   writeSuccess15694Local (writeSuccess156e4TakenTrace3 value) regs;
   writeSuccess15694Local (writeSuccess156e4TakenTrace4 value)
     (writeSuccess156e4TakenRegs regs)].
Definition writeSuccess156e4TakenObservations value regs global :=
  map (fun local => writeSuccess15694Observation local global)
    (writeSuccess156e4TakenLocals value regs).
Definition writeSuccess156e4FallthroughLocals value regs :=
  [writeSuccess15694Local (writeSuccess156e4FallthroughTrace value) regs;
   writeSuccess15694Local (writeSuccess156e4FallthroughTrace1 value) regs;
   writeSuccess15694Local (writeSuccess156e4FallthroughTrace2 value)
     (writeSuccess156e4FallthroughRegs regs)].
Definition writeSuccess156e4FallthroughObservations value regs global :=
  map (fun local => writeSuccess15694Observation local global)
    (writeSuccess156e4FallthroughLocals value regs).

Lemma writeSuccess156e4TakenSuffixPath regs global (value : bv 64) :
  regs !! "PC" = Some (RVal_Bits (Z_to_bv 64 0x156e4)) ->
  IslaInstructionPrefixPath
    (writeSuccess15694Local (writeSuccess156e4Trace10 value true) regs,
      global)
    (writeSuccess156e4TakenObservations value regs global)
    (writeSuccess15694Local tnil (writeSuccess156e4TakenRegs regs), global).
Proof.
  intros Hpc. unfold writeSuccess156e4TakenObservations,
    writeSuccess156e4TakenLocals.
  eapply IslaInstructionPrefixStep; first discriminate.
  { apply writeSuccessSeqSilent; first reflexivity.
    cbn [writeSuccess156e4Trace10 writeSuccess156e4Trace9
      writeSuccess156e4Trace10 writeSuccess156e4Trace9
      writeSuccess156e4Trace8 writeSuccess156e4Trace7
      writeSuccess156e4Trace6 writeSuccess156e4Trace5
      writeSuccess156e4Trace4 writeSuccess156e4Trace3
      writeSuccess156e4Trace2 writeSuccess156e4Trace1
      writeSuccess156e4TakenTrace writeSuccess156e4Branches
      writeSuccess156e4NextPc writeSuccess156e4TakenPc
      writeSuccessTraceTail a156e4].
    eapply CasesES with (es := writeSuccess156e4TakenTrace value).
    cbn. rewrite elem_of_cons. left. reflexivity. }
  eapply IslaInstructionPrefixStep; first discriminate.
  { apply writeSuccessSeqAssertTrue; first reflexivity.
    cbn [writeSuccess156e4TakenTrace writeSuccess156e4Branches
      writeSuccess156e4Trace10 writeSuccess156e4Trace9
      writeSuccess156e4Trace10 writeSuccess156e4Trace9
      writeSuccess156e4Trace8 writeSuccess156e4Trace7
      writeSuccess156e4Trace6 writeSuccess156e4Trace5
      writeSuccess156e4Trace4 writeSuccess156e4Trace3
      writeSuccess156e4Trace2 writeSuccess156e4Trace1
      writeSuccess156e4NextPc writeSuccess156e4TakenPc
      writeSuccessTraceTail a156e4]. eapply AssertS. reflexivity. }
  eapply IslaInstructionPrefixStep; first discriminate.
  { apply writeSuccessSeqSilent; first reflexivity.
    cbn [writeSuccess156e4TakenTrace1 writeSuccess156e4TakenTrace
      writeSuccess156e4Branches writeSuccess156e4Trace10
      writeSuccess156e4Trace9 writeSuccess156e4Trace10
      writeSuccess156e4Trace9 writeSuccess156e4Trace8
      writeSuccess156e4Trace7 writeSuccess156e4Trace6
      writeSuccess156e4Trace5 writeSuccess156e4Trace4
      writeSuccess156e4Trace3 writeSuccess156e4Trace2
      writeSuccess156e4Trace1 writeSuccess156e4NextPc
      writeSuccess156e4TakenPc writeSuccess156e4TakenBit
      writeSuccessTraceTail a156e4].
    eapply DefineConstS with (v := Val_Bits writeSuccess156e4TakenBit).
    reflexivity. }
  eapply IslaInstructionPrefixStep; first discriminate.
  { apply writeSuccessSeqBranchAddress with
      (target := RVal_Bits writeSuccess156e4TakenPc); first reflexivity.
    cbn [writeSuccess156e4TakenTrace2 writeSuccess156e4TakenTrace1
      writeSuccess156e4TakenTrace writeSuccess156e4Branches
      writeSuccess156e4Trace10 writeSuccess156e4Trace9
      writeSuccess156e4Trace10 writeSuccess156e4Trace9
      writeSuccess156e4Trace8 writeSuccess156e4Trace7
      writeSuccess156e4Trace6 writeSuccess156e4Trace5
      writeSuccess156e4Trace4 writeSuccess156e4Trace3
      writeSuccess156e4Trace2 writeSuccess156e4Trace1
      writeSuccess156e4NextPc writeSuccess156e4TakenPc
      writeSuccess156e4TakenBit writeSuccessTraceTail a156e4]. constructor. }
  eapply IslaInstructionPrefixStep; first discriminate.
  { eapply writeSuccessSeqWriteReg with
      (root := RVal_Bits (Z_to_bv 64 0x156e4))
      (value := RVal_Bits writeSuccess156e4TakenPc)
      (updated := RVal_Bits writeSuccess156e4TakenPc).
    - reflexivity.
    - cbn [writeSuccess156e4TakenTrace3 writeSuccess156e4TakenTrace2
        writeSuccess156e4TakenTrace1 writeSuccess156e4TakenTrace
        writeSuccess156e4Branches writeSuccess156e4Trace10
        writeSuccess156e4Trace9 writeSuccess156e4Trace10
        writeSuccess156e4Trace9 writeSuccess156e4Trace8
        writeSuccess156e4Trace7 writeSuccess156e4Trace6
        writeSuccess156e4Trace5 writeSuccess156e4Trace4
        writeSuccess156e4Trace3 writeSuccess156e4Trace2
        writeSuccess156e4Trace1 writeSuccess156e4NextPc
        writeSuccess156e4TakenPc writeSuccess156e4TakenBit
        writeSuccessTraceTail a156e4]. constructor.
    - exact Hpc.
    - reflexivity.
    - reflexivity. }
  apply IslaInstructionPrefixRefl.
Qed.

Lemma writeSuccess156e4FallthroughSuffixPath regs global (value : bv 64) :
  regs !! "PC" = Some (RVal_Bits (Z_to_bv 64 0x156e4)) ->
  IslaInstructionPrefixPath
    (writeSuccess15694Local (writeSuccess156e4Trace10 value false) regs,
      global)
    (writeSuccess156e4FallthroughObservations value regs global)
    (writeSuccess15694Local tnil
      (writeSuccess156e4FallthroughRegs regs), global).
Proof.
  intros Hpc. unfold writeSuccess156e4FallthroughObservations,
    writeSuccess156e4FallthroughLocals.
  eapply IslaInstructionPrefixStep; first discriminate.
  { apply writeSuccessSeqSilent; first reflexivity.
    cbn [writeSuccess156e4Trace10 writeSuccess156e4Trace9
      writeSuccess156e4Trace10 writeSuccess156e4Trace9
      writeSuccess156e4Trace8 writeSuccess156e4Trace7
      writeSuccess156e4Trace6 writeSuccess156e4Trace5
      writeSuccess156e4Trace4 writeSuccess156e4Trace3
      writeSuccess156e4Trace2 writeSuccess156e4Trace1
      writeSuccess156e4FallthroughTrace writeSuccess156e4Branches
      writeSuccess156e4NextPc writeSuccess156e4TakenPc
      writeSuccessTraceTail a156e4].
    eapply CasesES with (es := writeSuccess156e4FallthroughTrace value).
    cbn. rewrite elem_of_cons. right. rewrite elem_of_cons. left. reflexivity. }
  eapply IslaInstructionPrefixStep; first discriminate.
  { apply writeSuccessSeqAssertTrue; first reflexivity.
    cbn [writeSuccess156e4FallthroughTrace writeSuccess156e4Branches
      writeSuccess156e4Trace10 writeSuccess156e4Trace9
      writeSuccess156e4Trace10 writeSuccess156e4Trace9
      writeSuccess156e4Trace8 writeSuccess156e4Trace7
      writeSuccess156e4Trace6 writeSuccess156e4Trace5
      writeSuccess156e4Trace4 writeSuccess156e4Trace3
      writeSuccess156e4Trace2 writeSuccess156e4Trace1
      writeSuccess156e4NextPc writeSuccess156e4TakenPc
      writeSuccessTraceTail a156e4]. eapply AssertS. reflexivity. }
  eapply IslaInstructionPrefixStep; first discriminate.
  { eapply writeSuccessSeqWriteReg with
      (root := RVal_Bits (Z_to_bv 64 0x156e4))
      (value := RVal_Bits writeSuccess156e4NextPc)
      (updated := RVal_Bits writeSuccess156e4NextPc).
    - reflexivity.
    - cbn [writeSuccess156e4FallthroughTrace1
        writeSuccess156e4FallthroughTrace writeSuccess156e4Branches
        writeSuccess156e4Trace10 writeSuccess156e4Trace9
        writeSuccess156e4Trace10 writeSuccess156e4Trace9
        writeSuccess156e4Trace8 writeSuccess156e4Trace7
        writeSuccess156e4Trace6 writeSuccess156e4Trace5
        writeSuccess156e4Trace4 writeSuccess156e4Trace3
        writeSuccess156e4Trace2 writeSuccess156e4Trace1
        writeSuccess156e4NextPc writeSuccess156e4TakenPc
        writeSuccessTraceTail a156e4]. constructor.
    - exact Hpc.
    - reflexivity.
    - reflexivity. }
  apply IslaInstructionPrefixRefl.
Qed.

Print Assumptions writeSuccess156e4TakenSuffixPath.
Print Assumptions writeSuccess156e4FallthroughSuffixPath.

Definition writeSuccess156e4TakenAllObservations value regs global :=
  writeSuccess156e4CommonObservations value true regs global ++
  writeSuccess156e4TakenObservations value regs global ++
  [writeSuccess15694Observation
    (writeSuccess156e4TakenAfter regs global).1 global].
Definition writeSuccess156e4FallthroughAllObservations value regs global :=
  writeSuccess156e4CommonObservations value false regs global ++
  writeSuccess156e4FallthroughObservations value regs global ++
  [writeSuccess15694Observation
    (writeSuccess156e4FallthroughAfter regs global).1 global].

Lemma segment_156e4_taken_mstatus regs global (value : bv 64) :
  regs !! "PC" = Some (RVal_Bits (Z_to_bv 64 0x156e4)) ->
  regs !! "x9" = Some (RVal_Bits value) ->
  value <> (BV 64 0) ->
  global.(seq_instrs) !! Z_to_bv 64 0x156e4 = Some a156e4 ->
  global.(seq_instrs) !! Z_to_bv 64 0x15694 = Some a15694 ->
  eval_a_exp regs writeSuccess15694Mstatus = Some (Val_Bool true) ->
  IslaInstructionSegment (writeSuccess156e4Before regs global)
    (writeSuccess156e4TakenAllObservations value regs global)
    (writeSuccess156e4TakenAfter regs global).
Proof.
  intros Hpc Hx9 Hne Hcode Hnext Hmstatus.
  unfold writeSuccess156e4TakenAllObservations.
  eapply islaInstructionSegmentIntro with
    (prefix := writeSuccess156e4CommonObservations value true regs global ++
      writeSuccess156e4TakenObservations value regs global)
    (done := (writeSuccess15694Local tnil
      (writeSuccess156e4TakenRegs regs), global))
    (labels := []) (spawned := []).
  - split; first reflexivity. exists (Z_to_bv 64 0x156e4), a156e4.
    cbn. rewrite Hpc Hcode. repeat split; reflexivity.
  - eapply writeSuccessInstructionPrefixPathAppend.
    + eapply writeSuccess156e4CommonPath; eauto.
      apply writeSuccess156e4ConditionTaken. exact Hne.
    + apply writeSuccess156e4TakenSuffixPath. exact Hpc.
  - reflexivity.
  - apply writeSuccessSeqDoneTabled with (next := a15694) (trace := a15694).
    + reflexivity. + reflexivity. + constructor.
    + exists (Z_to_bv 64 0x15694). unfold writeSuccess156e4TakenRegs.
      rewrite lookup_insert. destruct writeSuccess156e4PcValues as (_ & ->).
      rewrite Hnext. repeat split; reflexivity.
  - left. split; first reflexivity. exists (Z_to_bv 64 0x15694), a15694.
    cbn. unfold writeSuccess156e4TakenRegs. rewrite lookup_insert.
    destruct writeSuccess156e4PcValues as (_ & ->).
    rewrite Hnext. repeat split; reflexivity.
Qed.

Lemma segment_156e4_fallthrough_mstatus regs global (value : bv 64) :
  regs !! "PC" = Some (RVal_Bits (Z_to_bv 64 0x156e4)) ->
  regs !! "x9" = Some (RVal_Bits value) ->
  value = (BV 64 0) ->
  global.(seq_instrs) !! Z_to_bv 64 0x156e4 = Some a156e4 ->
  global.(seq_instrs) !! Z_to_bv 64 0x156e8 = Some a156e8 ->
  eval_a_exp regs writeSuccess15694Mstatus = Some (Val_Bool true) ->
  IslaInstructionSegment (writeSuccess156e4Before regs global)
    (writeSuccess156e4FallthroughAllObservations value regs global)
    (writeSuccess156e4FallthroughAfter regs global).
Proof.
  intros Hpc Hx9 Heq Hcode Hnext Hmstatus.
  unfold writeSuccess156e4FallthroughAllObservations.
  eapply islaInstructionSegmentIntro with
    (prefix := writeSuccess156e4CommonObservations value false regs global ++
      writeSuccess156e4FallthroughObservations value regs global)
    (done := (writeSuccess15694Local tnil
      (writeSuccess156e4FallthroughRegs regs), global))
    (labels := []) (spawned := []).
  - split; first reflexivity. exists (Z_to_bv 64 0x156e4), a156e4.
    cbn. rewrite Hpc Hcode. repeat split; reflexivity.
  - eapply writeSuccessInstructionPrefixPathAppend.
    + eapply writeSuccess156e4CommonPath; eauto.
      apply writeSuccess156e4ConditionFallthrough. exact Heq.
    + apply writeSuccess156e4FallthroughSuffixPath. exact Hpc.
  - reflexivity.
  - apply writeSuccessSeqDoneTabled with (next := a156e8) (trace := a156e8).
    + reflexivity. + reflexivity. + constructor.
    + exists (Z_to_bv 64 0x156e8). unfold writeSuccess156e4FallthroughRegs.
      rewrite lookup_insert. destruct writeSuccess156e4PcValues as (-> & _).
      rewrite Hnext. repeat split; reflexivity.
  - left. split; first reflexivity. exists (Z_to_bv 64 0x156e8), a156e8.
    cbn. unfold writeSuccess156e4FallthroughRegs. rewrite lookup_insert.
    destruct writeSuccess156e4PcValues as (-> & _).
    rewrite Hnext. repeat split; reflexivity.
Qed.

Print Assumptions segment_156e4_taken_mstatus.
Print Assumptions segment_156e4_fallthrough_mstatus.

Definition writeSuccess156e4After (value : bv 64) regs global : IslaState :=
  if decide (value = (BV 64 0))
  then writeSuccess156e4FallthroughAfter regs global
  else writeSuccess156e4TakenAfter regs global.
Definition writeSuccess156e4Observations (value : bv 64) regs global :=
  if decide (value = (BV 64 0))
  then writeSuccess156e4FallthroughAllObservations value regs global
  else writeSuccess156e4TakenAllObservations value regs global.

Lemma segment_156e4_mstatus regs global (value : bv 64) :
  regs !! "PC" = Some (RVal_Bits (Z_to_bv 64 0x156e4)) ->
  regs !! "x9" = Some (RVal_Bits value) ->
  global.(seq_instrs) !! Z_to_bv 64 0x156e4 = Some a156e4 ->
  global.(seq_instrs) !! Z_to_bv 64 0x156e8 = Some a156e8 ->
  global.(seq_instrs) !! Z_to_bv 64 0x15694 = Some a15694 ->
  eval_a_exp regs writeSuccess15694Mstatus = Some (Val_Bool true) ->
  IslaInstructionSegment (writeSuccess156e4Before regs global)
    (writeSuccess156e4Observations value regs global)
    (writeSuccess156e4After value regs global).
Proof.
  intros Hpc Hx9 Hcode Hfall Htaken Hmstatus.
  unfold writeSuccess156e4Observations, writeSuccess156e4After.
  destruct (decide (value = (BV 64 0))) as [Heq|Hne].
  - eapply segment_156e4_fallthrough_mstatus; eauto.
  - eapply segment_156e4_taken_mstatus; eauto.
Qed.

Lemma segment_156e4 regs global (value : bv 64) :
  regs !! "PC" = Some (RVal_Bits (Z_to_bv 64 0x156e4)) ->
  regs !! "x9" = Some (RVal_Bits value) ->
  global.(seq_instrs) !! Z_to_bv 64 0x156e4 = Some a156e4 ->
  global.(seq_instrs) !! Z_to_bv 64 0x156e8 = Some a156e8 ->
  global.(seq_instrs) !! Z_to_bv 64 0x15694 = Some a15694 ->
  eval_a_exp regs writeSuccess15694Mstatus = Some (Val_Bool true) ->
  IslaInstructionSegment (writeSuccess156e4Before regs global)
    (writeSuccess156e4Observations value regs global)
    (writeSuccess156e4After value regs global).
Proof.
  intros Hpc Hx9 Hcode Hfall Htaken Hmstatus.
  eapply segment_156e4_mstatus; eauto.
Qed.

Definition writeSuccess156e4FinalRegs (value : bv 64) regs : reg_map :=
  if decide (value = (BV 64 0))
  then writeSuccess156e4FallthroughRegs regs
  else writeSuccess156e4TakenRegs regs.

Lemma writeSuccess156e4AfterRegs value regs global :
  (writeSuccess156e4After value regs global).1.(seq_regs) =
  writeSuccess156e4FinalRegs value regs.
Proof. unfold writeSuccess156e4After, writeSuccess156e4FinalRegs.
  destruct decide; reflexivity. Qed.

Lemma writeSuccess156e4RegsLookupOther regs (value : bv 64) reg :
  reg <> "PC" ->
  writeSuccess156e4FinalRegs value regs !! reg = regs !! reg.
Proof.
  intros Hreg. unfold writeSuccess156e4FinalRegs,
    writeSuccess156e4TakenRegs, writeSuccess156e4FallthroughRegs,
    writeSuccess15694Local. destruct decide.
  - rewrite lookup_insert_ne; last naive_solver. reflexivity.
  - rewrite lookup_insert_ne; last naive_solver. reflexivity.
Qed.

Lemma writeSuccess156e4RegsDom regs (value : bv 64) :
  regs !! "PC" = Some (RVal_Bits (Z_to_bv 64 0x156e4)) ->
  dom (writeSuccess156e4FinalRegs value regs) = dom regs.
Proof.
  intros Hpc. apply elem_of_dom_2 in Hpc.
  unfold writeSuccess156e4FinalRegs, writeSuccess156e4TakenRegs,
    writeSuccess156e4FallthroughRegs.
  destruct decide; rewrite dom_insert_L; set_solver.
Qed.

Print Assumptions segment_156e4_mstatus.
Print Assumptions segment_156e4.
Print Assumptions writeSuccess156e4RegsDom.
