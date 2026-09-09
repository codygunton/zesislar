(* Instantiated from the pinned 0x15690 beqz trace shape. *)
(* The renderer validates the pinned operands and endpoints. *)
From Coq Require Import Eqdep_dec Lists.List ZArith.ZArith.
Require Import isla.riscv64.riscv64.
Require Import IslaTraces.write_success_89.a15690.
Require Import IslaTraces.write_success_90.a15694.
Require Import IslaTraces.write_success_96.a156e8.
Require Import ZesuSsz.Contracts.InstructionBoundary.
Require Import ZesuSsz.Experiments.WriteSuccessSegmentAutomation.
Require Import ZesuSsz.Experiments.WriteSuccessCoverageAutomation.
Require Import ZesuSsz.Experiments.WriteSuccessSegment15694.

Import ListNotations.
Open Scope Z_scope.

Definition writeSuccess15690Alignment : a_exp :=
  AExp_Binop Eq
    (AExp_Unop (Extract 1 0) (AExp_Val (AVal_Var "PC" []) Mk_annot) Mk_annot)
    (AExp_Val (AVal_Bits (BV 2 0)) Mk_annot) Mk_annot.

Definition writeSuccess15690Condition (value : bv 64) : exp :=
  Binop Eq (Val (Val_Bits value) Mk_annot)
    (Val (Val_Bits (BV 64 0)) Mk_annot) Mk_annot.

Lemma writeSuccessBvnToBvSame n (value : bv n) :
  bvn_to_bv n (bv_to_bvn value) = Some value.
Proof.
  destruct value as [bits Hbits]. unfold bvn_to_bv. cbn.
  destruct (decide (n = n)) as [Heq|Hneq].
  - f_equal. symmetry. apply Eqdep_dec.eq_rect_eq_dec. apply N.eq_dec.
  - exfalso. apply Hneq. reflexivity.
Qed.

Local Opaque bvn_to_bv.

Lemma writeSuccess15690AlignmentHolds regs :
  regs !! "PC" = Some (RVal_Bits (Z_to_bv 64 0x15690)) ->
  eval_a_exp regs writeSuccess15690Alignment = Some (Val_Bool true).
Proof.
  intros Hpc. unfold writeSuccess15690Alignment. cbn. rewrite Hpc. vm_compute.
  reflexivity.
Qed.

Lemma writeSuccess15690ConditionTaken value :
  value = (BV 64 0) ->
  eval_exp (writeSuccess15690Condition value) = Some (Val_Bool true).
Proof.
  intros ->. unfold writeSuccess15690Condition. cbn.
  rewrite writeSuccessBvnToBvSame. cbn.
  case_bool_decide; last contradiction. reflexivity.
Qed.

Lemma writeSuccess15690ConditionFallthrough value :
  value <> (BV 64 0) ->
  eval_exp (writeSuccess15690Condition value) = Some (Val_Bool false).
Proof.
  intros Hne. unfold writeSuccess15690Condition. cbn.
  rewrite writeSuccessBvnToBvSame. cbn.
  case_bool_decide; first contradiction. reflexivity.
Qed.

Print Assumptions writeSuccess15690AlignmentHolds.
Print Assumptions writeSuccess15690ConditionTaken.
Print Assumptions writeSuccess15690ConditionFallthrough.

Definition writeSuccess15690NextPc : bv 64 :=
  (Z_to_bv 64 0x15690 + BV 64 4)%bv.
Definition writeSuccess15690TakenPc : bv 64 :=
  (Z_to_bv 64 0x15690 + BV 64 0x58)%bv.

Definition writeSuccess15690Trace1 (condition : bool) :=
  subst_trace (Val_Bits (BV 64 0)) 2 (writeSuccessTraceTail a15690).
Definition writeSuccess15690Trace2 (condition : bool) :=
  writeSuccessTraceTail (writeSuccess15690Trace1 condition).
Definition writeSuccess15690Trace3 (condition : bool) :=
  subst_trace (Val_Bits (Z_to_bv 64 0x15690)) 3
    (writeSuccessTraceTail (writeSuccess15690Trace2 condition)).
Definition writeSuccess15690Trace4 (condition : bool) :=
  writeSuccessTraceTail (writeSuccess15690Trace3 condition).
Definition writeSuccess15690Trace5 (condition : bool) :=
  writeSuccessTraceTail (writeSuccess15690Trace4 condition).
Definition writeSuccess15690Trace6 (condition : bool) :=
  subst_trace (Val_Bits writeSuccess15690NextPc) 4
    (writeSuccessTraceTail (writeSuccess15690Trace5 condition)).
Definition writeSuccess15690Trace7 (value : bv 64) (condition : bool) :=
  subst_trace (Val_Bits value) 5
    (writeSuccessTraceTail (writeSuccess15690Trace6 condition)).
Definition writeSuccess15690Trace8 (value : bv 64) (condition : bool) :=
  writeSuccessTraceTail (writeSuccess15690Trace7 value condition).
Definition writeSuccess15690Trace9 (value : bv 64) (condition : bool) :=
  subst_trace (Val_Bool condition) 6
    (writeSuccessTraceTail (writeSuccess15690Trace8 value condition)).
Definition writeSuccess15690Trace10 (value : bv 64) (condition : bool) :=
  subst_trace (Val_Bits writeSuccess15690TakenPc) 7
    (writeSuccessTraceTail (writeSuccess15690Trace9 value condition)).

Definition writeSuccess15690Branches (value : bv 64) (condition : bool) : list isla_trace :=
  match writeSuccess15690Trace10 value condition with
  | tcases branches => branches
  | _ => []
  end.
Definition writeSuccess15690TakenTrace (value : bv 64) :=
  nth 0 (writeSuccess15690Branches value true) tnil.
Definition writeSuccess15690TakenWrongTrace (value : bv 64) :=
  nth 1 (writeSuccess15690Branches value true) tnil.
Definition writeSuccess15690FallthroughTrace (value : bv 64) :=
  nth 1 (writeSuccess15690Branches value false) tnil.
Definition writeSuccess15690FallthroughWrongTrace (value : bv 64) :=
  nth 0 (writeSuccess15690Branches value false) tnil.

Lemma writeSuccess15690TakenBranchesExact value :
  writeSuccess15690Branches value true =
    [writeSuccess15690TakenTrace value;
     writeSuccess15690TakenWrongTrace value].
Proof.
  unfold writeSuccess15690Branches, writeSuccess15690TakenTrace,
    writeSuccess15690TakenWrongTrace.
  cbn [writeSuccess15690Trace10 writeSuccess15690Trace9
    writeSuccess15690Trace8 writeSuccess15690Trace7
    writeSuccess15690Trace6 writeSuccess15690Trace5
    writeSuccess15690Trace4 writeSuccess15690Trace3
    writeSuccess15690Trace2 writeSuccess15690Trace1
    writeSuccess15690NextPc writeSuccess15690TakenPc
    writeSuccessTraceTail a15690].
  reflexivity.
Qed.

Lemma writeSuccess15690FallthroughBranchesExact value :
  writeSuccess15690Branches value false =
    [writeSuccess15690FallthroughWrongTrace value;
     writeSuccess15690FallthroughTrace value].
Proof.
  unfold writeSuccess15690Branches, writeSuccess15690FallthroughTrace,
    writeSuccess15690FallthroughWrongTrace.
  cbn [writeSuccess15690Trace10 writeSuccess15690Trace9
    writeSuccess15690Trace8 writeSuccess15690Trace7
    writeSuccess15690Trace6 writeSuccess15690Trace5
    writeSuccess15690Trace4 writeSuccess15690Trace3
    writeSuccess15690Trace2 writeSuccess15690Trace1
    writeSuccess15690NextPc writeSuccess15690TakenPc
    writeSuccessTraceTail a15690].
  reflexivity.
Qed.
Definition writeSuccess15690TakenTrace1 (value : bv 64) :=
  writeSuccessTraceTail (writeSuccess15690TakenTrace value).
Definition writeSuccess15690TakenBit : bv 1 :=
  bv_extract 0 1 (bv_shiftr writeSuccess15690TakenPc (BV 64 1)).
Definition writeSuccess15690TakenTrace2 (value : bv 64) :=
  subst_trace (Val_Bits writeSuccess15690TakenBit) 9
    (writeSuccessTraceTail (writeSuccess15690TakenTrace1 value)).
Definition writeSuccess15690TakenTrace3 (value : bv 64) :=
  writeSuccessTraceTail (writeSuccess15690TakenTrace2 value).
Definition writeSuccess15690TakenTrace4 (value : bv 64) :=
  writeSuccessTraceTail (writeSuccess15690TakenTrace3 value).
Definition writeSuccess15690FallthroughTrace1 (value : bv 64) :=
  writeSuccessTraceTail (writeSuccess15690FallthroughTrace value).
Definition writeSuccess15690FallthroughTrace2 (value : bv 64) :=
  writeSuccessTraceTail (writeSuccess15690FallthroughTrace1 value).

Print Assumptions writeSuccess15690TakenBranchesExact.
Print Assumptions writeSuccess15690FallthroughBranchesExact.

Definition writeSuccess15690Before regs global : IslaState :=
  (writeSuccess15694Local a15690 regs, global).
Definition writeSuccess15690TakenRegs regs : reg_map :=
  <["PC" := RVal_Bits writeSuccess15690TakenPc]> regs.
Definition writeSuccess15690FallthroughRegs regs : reg_map :=
  <["PC" := RVal_Bits writeSuccess15690NextPc]> regs.
Definition writeSuccess15690TakenAfter regs global : IslaState :=
  (writeSuccess15694Local a156e8 (writeSuccess15690TakenRegs regs), global).
Definition writeSuccess15690FallthroughAfter regs global : IslaState :=
  (writeSuccess15694Local a15694 (writeSuccess15690FallthroughRegs regs), global).

Lemma writeSuccess15690PcValues :
  writeSuccess15690NextPc = Z_to_bv 64 0x15694 /\
  writeSuccess15690TakenPc = Z_to_bv 64 0x156e8.
Proof. vm_compute. split; apply bv_eq; reflexivity. Qed.

Lemma writeSuccessInstructionPrefixPathAppend before first middle second after :
  IslaInstructionPrefixPath before first middle ->
  IslaInstructionPrefixPath middle second after ->
  IslaInstructionPrefixPath before (first ++ second) after.
Proof.
  intros Hfirst Hsecond. induction Hfirst; cbn; first exact Hsecond.
  econstructor; eauto.
Qed.

Definition writeSuccess15690CommonLocals (value : bv 64)
    (condition : bool) regs :=
  [writeSuccess15694Local (writeSuccess15690Trace1 condition) regs;
   writeSuccess15694Local (writeSuccess15690Trace2 condition) regs;
   writeSuccess15694Local (writeSuccess15690Trace3 condition) regs;
   writeSuccess15694Local (writeSuccess15690Trace4 condition) regs;
   writeSuccess15694Local (writeSuccess15690Trace5 condition) regs;
   writeSuccess15694Local (writeSuccess15690Trace6 condition) regs;
   writeSuccess15694Local (writeSuccess15690Trace7 value condition) regs;
   writeSuccess15694Local (writeSuccess15690Trace8 value condition) regs;
   writeSuccess15694Local (writeSuccess15690Trace9 value condition) regs;
   writeSuccess15694Local (writeSuccess15690Trace10 value condition) regs].
Definition writeSuccess15690CommonObservations (value : bv 64)
    (condition : bool) regs global :=
  map (fun local => writeSuccess15694Observation local global)
    (writeSuccess15690CommonLocals value condition regs).

Lemma writeSuccess15690CommonPath regs global (value : bv 64)
    (condition : bool) :
  regs !! "PC" = Some (RVal_Bits (Z_to_bv 64 0x15690)) ->
  regs !! "x9" = Some (RVal_Bits value) ->
  eval_a_exp regs writeSuccess15694Mstatus = Some (Val_Bool true) ->
  eval_exp (writeSuccess15690Condition value) = Some (Val_Bool condition) ->
  IslaInstructionPrefixPath (writeSuccess15690Before regs global)
    (writeSuccess15690CommonObservations value condition regs global)
    (writeSuccess15694Local
      (writeSuccess15690Trace10 value condition) regs, global).
Proof.
  intros Hpc Hx9 Hmstatus Hcondition.
  have Halign := writeSuccess15690AlignmentHolds regs Hpc.
  unfold writeSuccess15690CommonObservations, writeSuccess15690CommonLocals.
  eapply IslaInstructionPrefixStep; first discriminate.
  { apply writeSuccessSeqSilent; first reflexivity.
    unfold writeSuccess15690Before, writeSuccess15694Local,
      writeSuccess15690Trace1, writeSuccessTraceTail, a15690. cbn.
    apply DeclareConstBitVecS' with (b := BV 64 0). }
  eapply IslaInstructionPrefixStep; first discriminate.
  { apply writeSuccessSeqAssume; first reflexivity.
    unfold writeSuccess15690Trace1, writeSuccessTraceTail, a15690. cbn.
    eapply AssumeS. exact Hmstatus. }
  eapply IslaInstructionPrefixStep; first discriminate.
  { apply writeSuccessSeqSilent; first reflexivity.
    unfold writeSuccess15690Trace2, writeSuccess15690Trace1,
      writeSuccessTraceTail, a15690. cbn.
    apply DeclareConstBitVecS' with (b := Z_to_bv 64 0x15690). }
  eapply IslaInstructionPrefixStep; first discriminate.
  { apply writeSuccessSeqAssume; first reflexivity.
    unfold writeSuccess15690Trace3, writeSuccess15690Trace2,
      writeSuccess15690Trace1, writeSuccessTraceTail, a15690. cbn.
    eapply AssumeS. exact Halign. }
  eapply IslaInstructionPrefixStep; first discriminate.
  { eapply writeSuccessSeqReadReg with
      (root := RVal_Bits (Z_to_bv 64 0x15690))
      (value := RVal_Bits (Z_to_bv 64 0x15690)).
    - reflexivity.
    - unfold writeSuccess15690Trace4, writeSuccess15690Trace3,
        writeSuccess15690Trace2, writeSuccess15690Trace1,
        writeSuccessTraceTail, a15690. cbn. constructor.
    - exact Hpc.
    - reflexivity.
    - reflexivity. }
  eapply IslaInstructionPrefixStep; first discriminate.
  { apply writeSuccessSeqSilent; first reflexivity.
    unfold writeSuccess15690Trace5, writeSuccess15690Trace4,
      writeSuccess15690Trace3, writeSuccess15690Trace2,
      writeSuccess15690Trace1, writeSuccess15690NextPc,
      writeSuccessTraceTail, a15690. cbn.
    eapply DefineConstS with (v := Val_Bits writeSuccess15690NextPc).
    reflexivity. }
  eapply IslaInstructionPrefixStep; first discriminate.
  { apply writeSuccessSeqSilent; first reflexivity.
    cbn [writeSuccess15690Trace6 writeSuccess15690Trace5
      writeSuccess15690Trace4 writeSuccess15690Trace3
      writeSuccess15690Trace2 writeSuccess15690Trace1
      writeSuccess15690NextPc writeSuccessTraceTail a15690].
    apply DeclareConstBitVecS' with (b := value). }
  eapply IslaInstructionPrefixStep; first discriminate.
  { eapply writeSuccessSeqReadReg with
      (root := RVal_Bits value) (value := RVal_Bits value).
    - reflexivity.
    - cbn [writeSuccess15690Trace7 writeSuccess15690Trace6
        writeSuccess15690Trace5 writeSuccess15690Trace4
        writeSuccess15690Trace3 writeSuccess15690Trace2
        writeSuccess15690Trace1 writeSuccess15690NextPc
        writeSuccessTraceTail a15690]. constructor.
    - exact Hx9.
    - reflexivity.
    - reflexivity. }
  eapply IslaInstructionPrefixStep; first discriminate.
  { apply writeSuccessSeqSilent; first reflexivity.
    cbn [writeSuccess15690Trace8 writeSuccess15690Trace7
      writeSuccess15690Trace8 writeSuccess15690Trace7
      writeSuccess15690Trace6 writeSuccess15690Trace5
      writeSuccess15690Trace4 writeSuccess15690Trace3
      writeSuccess15690Trace2 writeSuccess15690Trace1
      writeSuccess15690NextPc writeSuccessTraceTail a15690].
    eapply DefineConstS with (v := Val_Bool condition). exact Hcondition. }
  eapply IslaInstructionPrefixStep; first discriminate.
  { apply writeSuccessSeqSilent; first reflexivity.
    cbn [writeSuccess15690Trace9 writeSuccess15690Trace8
      writeSuccess15690Trace7 writeSuccess15690Trace6
      writeSuccess15690Trace5 writeSuccess15690Trace4
      writeSuccess15690Trace3 writeSuccess15690Trace2
      writeSuccess15690Trace1 writeSuccess15690NextPc
      writeSuccess15690TakenPc writeSuccessTraceTail a15690].
    eapply DefineConstS with (v := Val_Bits writeSuccess15690TakenPc).
    reflexivity. }
  apply IslaInstructionPrefixRefl.
Qed.

Print Assumptions writeSuccess15690CommonPath.

Definition writeSuccess15690TakenLocals value regs :=
  [writeSuccess15694Local (writeSuccess15690TakenTrace value) regs;
   writeSuccess15694Local (writeSuccess15690TakenTrace1 value) regs;
   writeSuccess15694Local (writeSuccess15690TakenTrace2 value) regs;
   writeSuccess15694Local (writeSuccess15690TakenTrace3 value) regs;
   writeSuccess15694Local (writeSuccess15690TakenTrace4 value)
     (writeSuccess15690TakenRegs regs)].
Definition writeSuccess15690TakenObservations value regs global :=
  map (fun local => writeSuccess15694Observation local global)
    (writeSuccess15690TakenLocals value regs).
Definition writeSuccess15690FallthroughLocals value regs :=
  [writeSuccess15694Local (writeSuccess15690FallthroughTrace value) regs;
   writeSuccess15694Local (writeSuccess15690FallthroughTrace1 value) regs;
   writeSuccess15694Local (writeSuccess15690FallthroughTrace2 value)
     (writeSuccess15690FallthroughRegs regs)].
Definition writeSuccess15690FallthroughObservations value regs global :=
  map (fun local => writeSuccess15694Observation local global)
    (writeSuccess15690FallthroughLocals value regs).

Lemma writeSuccess15690TakenSuffixPath regs global (value : bv 64) :
  regs !! "PC" = Some (RVal_Bits (Z_to_bv 64 0x15690)) ->
  IslaInstructionPrefixPath
    (writeSuccess15694Local (writeSuccess15690Trace10 value true) regs,
      global)
    (writeSuccess15690TakenObservations value regs global)
    (writeSuccess15694Local tnil (writeSuccess15690TakenRegs regs), global).
Proof.
  intros Hpc. unfold writeSuccess15690TakenObservations,
    writeSuccess15690TakenLocals.
  eapply IslaInstructionPrefixStep; first discriminate.
  { apply writeSuccessSeqSilent; first reflexivity.
    cbn [writeSuccess15690Trace10 writeSuccess15690Trace9
      writeSuccess15690Trace10 writeSuccess15690Trace9
      writeSuccess15690Trace8 writeSuccess15690Trace7
      writeSuccess15690Trace6 writeSuccess15690Trace5
      writeSuccess15690Trace4 writeSuccess15690Trace3
      writeSuccess15690Trace2 writeSuccess15690Trace1
      writeSuccess15690TakenTrace writeSuccess15690Branches
      writeSuccess15690NextPc writeSuccess15690TakenPc
      writeSuccessTraceTail a15690].
    eapply CasesES with (es := writeSuccess15690TakenTrace value).
    cbn. rewrite elem_of_cons. left. reflexivity. }
  eapply IslaInstructionPrefixStep; first discriminate.
  { apply writeSuccessSeqAssertTrue; first reflexivity.
    cbn [writeSuccess15690TakenTrace writeSuccess15690Branches
      writeSuccess15690Trace10 writeSuccess15690Trace9
      writeSuccess15690Trace10 writeSuccess15690Trace9
      writeSuccess15690Trace8 writeSuccess15690Trace7
      writeSuccess15690Trace6 writeSuccess15690Trace5
      writeSuccess15690Trace4 writeSuccess15690Trace3
      writeSuccess15690Trace2 writeSuccess15690Trace1
      writeSuccess15690NextPc writeSuccess15690TakenPc
      writeSuccessTraceTail a15690]. eapply AssertS. reflexivity. }
  eapply IslaInstructionPrefixStep; first discriminate.
  { apply writeSuccessSeqSilent; first reflexivity.
    cbn [writeSuccess15690TakenTrace1 writeSuccess15690TakenTrace
      writeSuccess15690Branches writeSuccess15690Trace10
      writeSuccess15690Trace9 writeSuccess15690Trace10
      writeSuccess15690Trace9 writeSuccess15690Trace8
      writeSuccess15690Trace7 writeSuccess15690Trace6
      writeSuccess15690Trace5 writeSuccess15690Trace4
      writeSuccess15690Trace3 writeSuccess15690Trace2
      writeSuccess15690Trace1 writeSuccess15690NextPc
      writeSuccess15690TakenPc writeSuccess15690TakenBit
      writeSuccessTraceTail a15690].
    eapply DefineConstS with (v := Val_Bits writeSuccess15690TakenBit).
    reflexivity. }
  eapply IslaInstructionPrefixStep; first discriminate.
  { apply writeSuccessSeqBranchAddress with
      (target := RVal_Bits writeSuccess15690TakenPc); first reflexivity.
    cbn [writeSuccess15690TakenTrace2 writeSuccess15690TakenTrace1
      writeSuccess15690TakenTrace writeSuccess15690Branches
      writeSuccess15690Trace10 writeSuccess15690Trace9
      writeSuccess15690Trace10 writeSuccess15690Trace9
      writeSuccess15690Trace8 writeSuccess15690Trace7
      writeSuccess15690Trace6 writeSuccess15690Trace5
      writeSuccess15690Trace4 writeSuccess15690Trace3
      writeSuccess15690Trace2 writeSuccess15690Trace1
      writeSuccess15690NextPc writeSuccess15690TakenPc
      writeSuccess15690TakenBit writeSuccessTraceTail a15690]. constructor. }
  eapply IslaInstructionPrefixStep; first discriminate.
  { eapply writeSuccessSeqWriteReg with
      (root := RVal_Bits (Z_to_bv 64 0x15690))
      (value := RVal_Bits writeSuccess15690TakenPc)
      (updated := RVal_Bits writeSuccess15690TakenPc).
    - reflexivity.
    - cbn [writeSuccess15690TakenTrace3 writeSuccess15690TakenTrace2
        writeSuccess15690TakenTrace1 writeSuccess15690TakenTrace
        writeSuccess15690Branches writeSuccess15690Trace10
        writeSuccess15690Trace9 writeSuccess15690Trace10
        writeSuccess15690Trace9 writeSuccess15690Trace8
        writeSuccess15690Trace7 writeSuccess15690Trace6
        writeSuccess15690Trace5 writeSuccess15690Trace4
        writeSuccess15690Trace3 writeSuccess15690Trace2
        writeSuccess15690Trace1 writeSuccess15690NextPc
        writeSuccess15690TakenPc writeSuccess15690TakenBit
        writeSuccessTraceTail a15690]. constructor.
    - exact Hpc.
    - reflexivity.
    - reflexivity. }
  apply IslaInstructionPrefixRefl.
Qed.

Lemma writeSuccess15690FallthroughSuffixPath regs global (value : bv 64) :
  regs !! "PC" = Some (RVal_Bits (Z_to_bv 64 0x15690)) ->
  IslaInstructionPrefixPath
    (writeSuccess15694Local (writeSuccess15690Trace10 value false) regs,
      global)
    (writeSuccess15690FallthroughObservations value regs global)
    (writeSuccess15694Local tnil
      (writeSuccess15690FallthroughRegs regs), global).
Proof.
  intros Hpc. unfold writeSuccess15690FallthroughObservations,
    writeSuccess15690FallthroughLocals.
  eapply IslaInstructionPrefixStep; first discriminate.
  { apply writeSuccessSeqSilent; first reflexivity.
    cbn [writeSuccess15690Trace10 writeSuccess15690Trace9
      writeSuccess15690Trace10 writeSuccess15690Trace9
      writeSuccess15690Trace8 writeSuccess15690Trace7
      writeSuccess15690Trace6 writeSuccess15690Trace5
      writeSuccess15690Trace4 writeSuccess15690Trace3
      writeSuccess15690Trace2 writeSuccess15690Trace1
      writeSuccess15690FallthroughTrace writeSuccess15690Branches
      writeSuccess15690NextPc writeSuccess15690TakenPc
      writeSuccessTraceTail a15690].
    eapply CasesES with (es := writeSuccess15690FallthroughTrace value).
    cbn. rewrite elem_of_cons. right. rewrite elem_of_cons. left. reflexivity. }
  eapply IslaInstructionPrefixStep; first discriminate.
  { apply writeSuccessSeqAssertTrue; first reflexivity.
    cbn [writeSuccess15690FallthroughTrace writeSuccess15690Branches
      writeSuccess15690Trace10 writeSuccess15690Trace9
      writeSuccess15690Trace10 writeSuccess15690Trace9
      writeSuccess15690Trace8 writeSuccess15690Trace7
      writeSuccess15690Trace6 writeSuccess15690Trace5
      writeSuccess15690Trace4 writeSuccess15690Trace3
      writeSuccess15690Trace2 writeSuccess15690Trace1
      writeSuccess15690NextPc writeSuccess15690TakenPc
      writeSuccessTraceTail a15690]. eapply AssertS. reflexivity. }
  eapply IslaInstructionPrefixStep; first discriminate.
  { eapply writeSuccessSeqWriteReg with
      (root := RVal_Bits (Z_to_bv 64 0x15690))
      (value := RVal_Bits writeSuccess15690NextPc)
      (updated := RVal_Bits writeSuccess15690NextPc).
    - reflexivity.
    - cbn [writeSuccess15690FallthroughTrace1
        writeSuccess15690FallthroughTrace writeSuccess15690Branches
        writeSuccess15690Trace10 writeSuccess15690Trace9
        writeSuccess15690Trace10 writeSuccess15690Trace9
        writeSuccess15690Trace8 writeSuccess15690Trace7
        writeSuccess15690Trace6 writeSuccess15690Trace5
        writeSuccess15690Trace4 writeSuccess15690Trace3
        writeSuccess15690Trace2 writeSuccess15690Trace1
        writeSuccess15690NextPc writeSuccess15690TakenPc
        writeSuccessTraceTail a15690]. constructor.
    - exact Hpc.
    - reflexivity.
    - reflexivity. }
  apply IslaInstructionPrefixRefl.
Qed.

Print Assumptions writeSuccess15690TakenSuffixPath.
Print Assumptions writeSuccess15690FallthroughSuffixPath.

Definition writeSuccess15690TakenAllObservations value regs global :=
  writeSuccess15690CommonObservations value true regs global ++
  writeSuccess15690TakenObservations value regs global ++
  [writeSuccess15694Observation
    (writeSuccess15690TakenAfter regs global).1 global].
Definition writeSuccess15690FallthroughAllObservations value regs global :=
  writeSuccess15690CommonObservations value false regs global ++
  writeSuccess15690FallthroughObservations value regs global ++
  [writeSuccess15694Observation
    (writeSuccess15690FallthroughAfter regs global).1 global].

Lemma segment_15690_taken_mstatus regs global (value : bv 64) :
  regs !! "PC" = Some (RVal_Bits (Z_to_bv 64 0x15690)) ->
  regs !! "x9" = Some (RVal_Bits value) ->
  value = (BV 64 0) ->
  global.(seq_instrs) !! Z_to_bv 64 0x15690 = Some a15690 ->
  global.(seq_instrs) !! Z_to_bv 64 0x156e8 = Some a156e8 ->
  eval_a_exp regs writeSuccess15694Mstatus = Some (Val_Bool true) ->
  IslaInstructionSegment (writeSuccess15690Before regs global)
    (writeSuccess15690TakenAllObservations value regs global)
    (writeSuccess15690TakenAfter regs global).
Proof.
  intros Hpc Hx9 Hne Hcode Hnext Hmstatus.
  unfold writeSuccess15690TakenAllObservations.
  eapply islaInstructionSegmentIntro with
    (prefix := writeSuccess15690CommonObservations value true regs global ++
      writeSuccess15690TakenObservations value regs global)
    (done := (writeSuccess15694Local tnil
      (writeSuccess15690TakenRegs regs), global))
    (labels := []) (spawned := []).
  - split; first reflexivity. exists (Z_to_bv 64 0x15690), a15690.
    cbn. rewrite Hpc Hcode. repeat split; reflexivity.
  - eapply writeSuccessInstructionPrefixPathAppend.
    + eapply writeSuccess15690CommonPath; eauto.
      apply writeSuccess15690ConditionTaken. exact Hne.
    + apply writeSuccess15690TakenSuffixPath. exact Hpc.
  - reflexivity.
  - apply writeSuccessSeqDoneTabled with (next := a156e8) (trace := a156e8).
    + reflexivity. + reflexivity. + constructor.
    + exists (Z_to_bv 64 0x156e8). unfold writeSuccess15690TakenRegs.
      rewrite lookup_insert. destruct writeSuccess15690PcValues as (_ & ->).
      rewrite Hnext. repeat split; reflexivity.
  - left. split; first reflexivity. exists (Z_to_bv 64 0x156e8), a156e8.
    cbn. unfold writeSuccess15690TakenRegs. rewrite lookup_insert.
    destruct writeSuccess15690PcValues as (_ & ->).
    rewrite Hnext. repeat split; reflexivity.
Qed.

Lemma segment_15690_fallthrough_mstatus regs global (value : bv 64) :
  regs !! "PC" = Some (RVal_Bits (Z_to_bv 64 0x15690)) ->
  regs !! "x9" = Some (RVal_Bits value) ->
  value <> (BV 64 0) ->
  global.(seq_instrs) !! Z_to_bv 64 0x15690 = Some a15690 ->
  global.(seq_instrs) !! Z_to_bv 64 0x15694 = Some a15694 ->
  eval_a_exp regs writeSuccess15694Mstatus = Some (Val_Bool true) ->
  IslaInstructionSegment (writeSuccess15690Before regs global)
    (writeSuccess15690FallthroughAllObservations value regs global)
    (writeSuccess15690FallthroughAfter regs global).
Proof.
  intros Hpc Hx9 Heq Hcode Hnext Hmstatus.
  unfold writeSuccess15690FallthroughAllObservations.
  eapply islaInstructionSegmentIntro with
    (prefix := writeSuccess15690CommonObservations value false regs global ++
      writeSuccess15690FallthroughObservations value regs global)
    (done := (writeSuccess15694Local tnil
      (writeSuccess15690FallthroughRegs regs), global))
    (labels := []) (spawned := []).
  - split; first reflexivity. exists (Z_to_bv 64 0x15690), a15690.
    cbn. rewrite Hpc Hcode. repeat split; reflexivity.
  - eapply writeSuccessInstructionPrefixPathAppend.
    + eapply writeSuccess15690CommonPath; eauto.
      apply writeSuccess15690ConditionFallthrough. exact Heq.
    + apply writeSuccess15690FallthroughSuffixPath. exact Hpc.
  - reflexivity.
  - apply writeSuccessSeqDoneTabled with (next := a15694) (trace := a15694).
    + reflexivity. + reflexivity. + constructor.
    + exists (Z_to_bv 64 0x15694). unfold writeSuccess15690FallthroughRegs.
      rewrite lookup_insert. destruct writeSuccess15690PcValues as (-> & _).
      rewrite Hnext. repeat split; reflexivity.
  - left. split; first reflexivity. exists (Z_to_bv 64 0x15694), a15694.
    cbn. unfold writeSuccess15690FallthroughRegs. rewrite lookup_insert.
    destruct writeSuccess15690PcValues as (-> & _).
    rewrite Hnext. repeat split; reflexivity.
Qed.

Print Assumptions segment_15690_taken_mstatus.
Print Assumptions segment_15690_fallthrough_mstatus.

Definition writeSuccess15690After (value : bv 64) regs global : IslaState :=
  if decide (value = (BV 64 0))
  then writeSuccess15690TakenAfter regs global
  else writeSuccess15690FallthroughAfter regs global.
Definition writeSuccess15690Observations (value : bv 64) regs global :=
  if decide (value = (BV 64 0))
  then writeSuccess15690TakenAllObservations value regs global
  else writeSuccess15690FallthroughAllObservations value regs global.

Lemma segment_15690_mstatus regs global (value : bv 64) :
  regs !! "PC" = Some (RVal_Bits (Z_to_bv 64 0x15690)) ->
  regs !! "x9" = Some (RVal_Bits value) ->
  global.(seq_instrs) !! Z_to_bv 64 0x15690 = Some a15690 ->
  global.(seq_instrs) !! Z_to_bv 64 0x15694 = Some a15694 ->
  global.(seq_instrs) !! Z_to_bv 64 0x156e8 = Some a156e8 ->
  eval_a_exp regs writeSuccess15694Mstatus = Some (Val_Bool true) ->
  IslaInstructionSegment (writeSuccess15690Before regs global)
    (writeSuccess15690Observations value regs global)
    (writeSuccess15690After value regs global).
Proof.
  intros Hpc Hx9 Hcode Hfall Htaken Hmstatus.
  unfold writeSuccess15690Observations, writeSuccess15690After.
  destruct (decide (value = (BV 64 0))) as [Heq|Hne].
  - eapply segment_15690_taken_mstatus; eauto.
  - eapply segment_15690_fallthrough_mstatus; eauto.
Qed.

Lemma segment_15690 regs global (value : bv 64) :
  regs !! "PC" = Some (RVal_Bits (Z_to_bv 64 0x15690)) ->
  regs !! "x9" = Some (RVal_Bits value) ->
  global.(seq_instrs) !! Z_to_bv 64 0x15690 = Some a15690 ->
  global.(seq_instrs) !! Z_to_bv 64 0x15694 = Some a15694 ->
  global.(seq_instrs) !! Z_to_bv 64 0x156e8 = Some a156e8 ->
  eval_a_exp regs writeSuccess15694Mstatus = Some (Val_Bool true) ->
  IslaInstructionSegment (writeSuccess15690Before regs global)
    (writeSuccess15690Observations value regs global)
    (writeSuccess15690After value regs global).
Proof.
  intros Hpc Hx9 Hcode Hfall Htaken Hmstatus.
  eapply segment_15690_mstatus; eauto.
Qed.

Definition writeSuccess15690FinalRegs (value : bv 64) regs : reg_map :=
  if decide (value = (BV 64 0))
  then writeSuccess15690TakenRegs regs
  else writeSuccess15690FallthroughRegs regs.

Lemma writeSuccess15690AfterRegs value regs global :
  (writeSuccess15690After value regs global).1.(seq_regs) =
  writeSuccess15690FinalRegs value regs.
Proof. unfold writeSuccess15690After, writeSuccess15690FinalRegs.
  destruct decide; reflexivity. Qed.

Lemma writeSuccess15690RegsLookupOther regs (value : bv 64) reg :
  reg <> "PC" ->
  writeSuccess15690FinalRegs value regs !! reg = regs !! reg.
Proof.
  intros Hreg. unfold writeSuccess15690FinalRegs,
    writeSuccess15690TakenRegs, writeSuccess15690FallthroughRegs,
    writeSuccess15694Local. destruct decide.
  - rewrite lookup_insert_ne; last naive_solver. reflexivity.
  - rewrite lookup_insert_ne; last naive_solver. reflexivity.
Qed.

Lemma writeSuccess15690RegsDom regs (value : bv 64) :
  regs !! "PC" = Some (RVal_Bits (Z_to_bv 64 0x15690)) ->
  dom (writeSuccess15690FinalRegs value regs) = dom regs.
Proof.
  intros Hpc. apply elem_of_dom_2 in Hpc.
  unfold writeSuccess15690FinalRegs, writeSuccess15690TakenRegs,
    writeSuccess15690FallthroughRegs.
  destruct decide; rewrite dom_insert_L; set_solver.
Qed.

Print Assumptions segment_15690_mstatus.
Print Assumptions segment_15690.
Print Assumptions writeSuccess15690RegsDom.
