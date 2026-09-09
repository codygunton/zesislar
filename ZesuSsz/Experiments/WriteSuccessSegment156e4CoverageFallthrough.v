(* Generated from the pinned bnez trace shape. *)
(* The renderer validates the pinned operands and endpoints. *)
From Coq Require Import Lists.List.
Require Import isla.riscv64.riscv64.
Require Import IslaTraces.write_success_95.a156e4.
Require Import IslaTraces.write_success_96.a156e8.
Require Import ZesuSsz.Contracts.InstructionBoundary.
Require Import ZesuSsz.Experiments.WriteSuccessSegmentAutomation.
Require Import ZesuSsz.Experiments.WriteSuccessCoverageAutomation.
Require Import ZesuSsz.Experiments.WriteSuccessSegment15694.
Require Import ZesuSsz.Experiments.WriteSuccessSegment156e4.

Import ListNotations.

Ltac unfold_write_success_156e4_fallthrough_branch :=
  cbn [writeSuccess156e4Trace10 writeSuccess156e4Trace9
    writeSuccess156e4Trace10 writeSuccess156e4Trace9
    writeSuccess156e4Trace8 writeSuccess156e4Trace7
    writeSuccess156e4Trace6 writeSuccess156e4Trace5
    writeSuccess156e4Trace4 writeSuccess156e4Trace3
    writeSuccess156e4Trace2 writeSuccess156e4Trace1
    writeSuccess156e4TakenTrace writeSuccess156e4FallthroughTrace
    writeSuccess156e4Branches writeSuccess156e4NextPc
    writeSuccess156e4TakenPc writeSuccessTraceTail a156e4].

Ltac unfold_write_success_156e4_fallthrough :=
  cbn [writeSuccess156e4FallthroughTrace2
    writeSuccess156e4FallthroughTrace1
    writeSuccess156e4FallthroughTrace writeSuccess156e4Branches
    writeSuccess156e4Trace10 writeSuccess156e4Trace9
    writeSuccess156e4Trace10 writeSuccess156e4Trace9
    writeSuccess156e4Trace8 writeSuccess156e4Trace7
    writeSuccess156e4Trace6 writeSuccess156e4Trace5
    writeSuccess156e4Trace4 writeSuccess156e4Trace3
    writeSuccess156e4Trace2 writeSuccess156e4Trace1
    writeSuccess156e4NextPc writeSuccess156e4TakenPc
    writeSuccessTraceTail a156e4].

Lemma segment_156e4_fallthrough_suffix_covered regs global (value : bv 64)
    prefix10 done labels spawned after :
  regs !! "PC" = Some (RVal_Bits (Z_to_bv 64 0x156e4)) ->
  global.(seq_instrs) !! Z_to_bv 64 0x156e8 = Some a156e8 ->
  IslaInstructionPrefixPath
    (writeSuccess15694Local (writeSuccess156e4Trace10 value false) regs,
      global) prefix10 done ->
  done.1.(seq_trace) = tnil ->
  seq_step done.1 done.2 labels after.1 after.2 spawned ->
  after = writeSuccess156e4FallthroughAfter regs global /\
  prefix10 ++ ({| microLabels := labels; microAfter := after |} :: []) =
    writeSuccess156e4FallthroughObservations value regs global ++
    [writeSuccess15694Observation
      (writeSuccess156e4FallthroughAfter regs global).1 global].
Proof.
  intros Hpc Hnext Hprefix10 Hnil Hdone.
  have HdoneNb := seqStepSourceBlocking _ _ _ _ _ _ Hdone.
  destruct (writeSuccess15694TakeStep _ _ _ Hprefix10
    ltac:(unfold_write_success_156e4_fallthrough_branch; discriminate)
    Hnil HdoneNb) as
    (? & local13 & global13 & ? & prefix13 & Hobs12 & Hstep12 & Hnb13 & Hprefix13).
  eapply writeSuccessCasesCovered in Hstep12.
  2: { unfold_write_success_156e4_fallthrough_branch. reflexivity. }
  destruct Hstep12 as (branch & Hbranch & -> & -> & -> & ->).
  unfold_write_success_156e4_fallthrough_branch.
  simpl in Hbranch. rewrite elem_of_cons in Hbranch.
  destruct Hbranch as [-> | Hbranch].
  - destruct (writeSuccess15694TakeStep _ _ _ Hprefix13
      ltac:(cbn; discriminate) Hnil HdoneNb) as
      (? & wrongLocal & wrongGlobal & ? & wrongPrefix & ? & Hwrong & HwrongNb & ?).
    eapply writeSuccessAssertFalseBlocks in Hwrong.
    2: reflexivity. 2: reflexivity.
    rewrite HwrongNb in Hwrong. discriminate.
  - rewrite elem_of_cons in Hbranch. rewrite elem_of_nil in Hbranch.
    destruct Hbranch as [-> | Hbranch]; last contradiction.
    destruct (writeSuccess15694TakeStep _ _ _ Hprefix13
      ltac:(cbn; discriminate) Hnil HdoneNb) as
      (? & local14 & global14 & ? & prefix14 & Hobs13 & Hstep13 & Hnb14 & Hprefix14).
    eapply writeSuccessAssertCovered in Hstep13.
    2: reflexivity. 2: reflexivity. 2: exact Hnb14.
    destruct Hstep13 as (-> & -> & -> & ->).
    destruct (writeSuccess15694TakeStep _ _ _ Hprefix14
      ltac:(unfold_write_success_156e4_fallthrough; discriminate)
      Hnil HdoneNb) as
      (? & local15 & global15 & ? & prefix15 & Hobs14 & Hstep14 & ? & Hprefix15).
    eapply writeSuccessWriteRegCovered in Hstep14.
    2: reflexivity. 2: exact Hpc. 2: reflexivity. 2: reflexivity.
    destruct Hstep14 as (-> & -> & -> & ->).
    inversion Hprefix15; subst; last contradiction.
    eapply writeSuccessDoneTabledCovered in Hdone.
    2: reflexivity.
    2: { unfold writeSuccess156e4FallthroughRegs. rewrite lookup_insert.
         reflexivity. }
    2: { destruct writeSuccess156e4PcValues as (-> & _). exact Hnext. }
    destruct Hdone as (Hlabels & HafterLocal & HafterGlobal & Hspawned).
    subst labels spawned. destruct after as [afterLocal afterGlobal].
    cbn in HafterLocal, HafterGlobal |- *. subst afterLocal afterGlobal.
    split; first reflexivity.
    unfold writeSuccess156e4FallthroughObservations,
      writeSuccess156e4FallthroughLocals. cbn. reflexivity.
Qed.

Print Assumptions segment_156e4_fallthrough_suffix_covered.
