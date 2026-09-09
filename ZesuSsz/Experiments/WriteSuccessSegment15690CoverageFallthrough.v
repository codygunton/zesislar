(* Instantiated from the pinned 0x15690 beqz trace shape. *)
(* The renderer validates the pinned operands and endpoints. *)
From Coq Require Import Lists.List.
Require Import isla.riscv64.riscv64.
Require Import IslaTraces.write_success_89.a15690.
Require Import IslaTraces.write_success_90.a15694.
Require Import ZesuSsz.Contracts.InstructionBoundary.
Require Import ZesuSsz.Experiments.WriteSuccessSegmentAutomation.
Require Import ZesuSsz.Experiments.WriteSuccessCoverageAutomation.
Require Import ZesuSsz.Experiments.WriteSuccessSegment15694.
Require Import ZesuSsz.Experiments.WriteSuccessSegment15690.

Import ListNotations.

Ltac unfold_write_success_15690_fallthrough_branch :=
  cbn [writeSuccess15690Trace10 writeSuccess15690Trace9
    writeSuccess15690Trace10 writeSuccess15690Trace9
    writeSuccess15690Trace8 writeSuccess15690Trace7
    writeSuccess15690Trace6 writeSuccess15690Trace5
    writeSuccess15690Trace4 writeSuccess15690Trace3
    writeSuccess15690Trace2 writeSuccess15690Trace1
    writeSuccess15690TakenTrace writeSuccess15690FallthroughTrace
    writeSuccess15690Branches writeSuccess15690NextPc
    writeSuccess15690TakenPc writeSuccessTraceTail a15690].

Ltac unfold_write_success_15690_fallthrough :=
  cbn [writeSuccess15690FallthroughTrace2
    writeSuccess15690FallthroughTrace1
    writeSuccess15690FallthroughTrace writeSuccess15690Branches
    writeSuccess15690Trace10 writeSuccess15690Trace9
    writeSuccess15690Trace10 writeSuccess15690Trace9
    writeSuccess15690Trace8 writeSuccess15690Trace7
    writeSuccess15690Trace6 writeSuccess15690Trace5
    writeSuccess15690Trace4 writeSuccess15690Trace3
    writeSuccess15690Trace2 writeSuccess15690Trace1
    writeSuccess15690NextPc writeSuccess15690TakenPc
    writeSuccessTraceTail a15690].

Lemma segment_15690_fallthrough_suffix_covered regs global (value : bv 64)
    prefix10 done labels spawned after :
  regs !! "PC" = Some (RVal_Bits (Z_to_bv 64 0x15690)) ->
  global.(seq_instrs) !! Z_to_bv 64 0x15694 = Some a15694 ->
  IslaInstructionPrefixPath
    (writeSuccess15694Local (writeSuccess15690Trace10 value false) regs,
      global) prefix10 done ->
  done.1.(seq_trace) = tnil ->
  seq_step done.1 done.2 labels after.1 after.2 spawned ->
  after = writeSuccess15690FallthroughAfter regs global /\
  prefix10 ++ ({| microLabels := labels; microAfter := after |} :: []) =
    writeSuccess15690FallthroughObservations value regs global ++
    [writeSuccess15694Observation
      (writeSuccess15690FallthroughAfter regs global).1 global].
Proof.
  intros Hpc Hnext Hprefix10 Hnil Hdone.
  have HdoneNb := seqStepSourceBlocking _ _ _ _ _ _ Hdone.
  destruct (writeSuccess15694TakeStep _ _ _ Hprefix10
    ltac:(unfold_write_success_15690_fallthrough_branch; discriminate)
    Hnil HdoneNb) as
    (? & local13 & global13 & ? & prefix13 & Hobs12 & Hstep12 & Hnb13 & Hprefix13).
  eapply writeSuccessCasesCovered in Hstep12.
  2: { unfold_write_success_15690_fallthrough_branch. reflexivity. }
  destruct Hstep12 as (branch & Hbranch & -> & -> & -> & ->).
  unfold_write_success_15690_fallthrough_branch.
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
      ltac:(unfold_write_success_15690_fallthrough; discriminate)
      Hnil HdoneNb) as
      (? & local15 & global15 & ? & prefix15 & Hobs14 & Hstep14 & ? & Hprefix15).
    eapply writeSuccessWriteRegCovered in Hstep14.
    2: reflexivity. 2: exact Hpc. 2: reflexivity. 2: reflexivity.
    destruct Hstep14 as (-> & -> & -> & ->).
    inversion Hprefix15; subst; last contradiction.
    eapply writeSuccessDoneTabledCovered in Hdone.
    2: reflexivity.
    2: { unfold writeSuccess15690FallthroughRegs. rewrite lookup_insert.
         reflexivity. }
    2: { destruct writeSuccess15690PcValues as (-> & _). exact Hnext. }
    destruct Hdone as (Hlabels & HafterLocal & HafterGlobal & Hspawned).
    subst labels spawned. destruct after as [afterLocal afterGlobal].
    cbn in HafterLocal, HafterGlobal |- *. subst afterLocal afterGlobal.
    split; first reflexivity.
    unfold writeSuccess15690FallthroughObservations,
      writeSuccess15690FallthroughLocals. cbn. reflexivity.
Qed.

Print Assumptions segment_15690_fallthrough_suffix_covered.
