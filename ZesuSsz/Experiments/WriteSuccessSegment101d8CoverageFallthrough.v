From Coq Require Import Lists.List.
Require Import isla.riscv64.riscv64.
Require Import IslaTraces.write_success_02.a101d8.
Require Import IslaTraces.write_success_02.a101dc.
Require Import ZesuSsz.Contracts.InstructionBoundary.
Require Import ZesuSsz.Experiments.WriteSuccessSegmentAutomation.
Require Import ZesuSsz.Experiments.WriteSuccessCoverageAutomation.
Require Import ZesuSsz.Experiments.WriteSuccessSegment15694.
Require Import ZesuSsz.Experiments.WriteSuccessSegment101d8.

Import ListNotations.

Ltac unfold_write_success_101d8_fallthrough_branch :=
  cbn [writeSuccess101d8Trace12 writeSuccess101d8Trace11
    writeSuccess101d8Trace10 writeSuccess101d8Trace9
    writeSuccess101d8Trace8 writeSuccess101d8Trace7
    writeSuccess101d8Trace6 writeSuccess101d8Trace5
    writeSuccess101d8Trace4 writeSuccess101d8Trace3
    writeSuccess101d8Trace2 writeSuccess101d8Trace1
    writeSuccess101d8TakenTrace writeSuccess101d8FallthroughTrace
    writeSuccess101d8Branches writeSuccess101d8NextPc
    writeSuccess101d8TakenPc writeSuccessTraceTail a101d8].

Ltac unfold_write_success_101d8_fallthrough :=
  cbn [writeSuccess101d8FallthroughTrace2
    writeSuccess101d8FallthroughTrace1
    writeSuccess101d8FallthroughTrace writeSuccess101d8Branches
    writeSuccess101d8Trace12 writeSuccess101d8Trace11
    writeSuccess101d8Trace10 writeSuccess101d8Trace9
    writeSuccess101d8Trace8 writeSuccess101d8Trace7
    writeSuccess101d8Trace6 writeSuccess101d8Trace5
    writeSuccess101d8Trace4 writeSuccess101d8Trace3
    writeSuccess101d8Trace2 writeSuccess101d8Trace1
    writeSuccess101d8NextPc writeSuccess101d8TakenPc
    writeSuccessTraceTail a101d8].

Lemma segment_101d8_fallthrough_suffix_covered regs global (left right : bv 64)
    prefix12 done labels spawned after :
  regs !! "PC" = Some (RVal_Bits (Z_to_bv 64 0x101d8)) ->
  global.(seq_instrs) !! Z_to_bv 64 0x101dc = Some a101dc ->
  IslaInstructionPrefixPath
    (writeSuccess15694Local (writeSuccess101d8Trace12 left right false) regs,
      global) prefix12 done ->
  done.1.(seq_trace) = tnil ->
  seq_step done.1 done.2 labels after.1 after.2 spawned ->
  after = writeSuccess101d8FallthroughAfter regs global /\
  prefix12 ++ ({| microLabels := labels; microAfter := after |} :: []) =
    writeSuccess101d8FallthroughObservations left right regs global ++
    [writeSuccess15694Observation
      (writeSuccess101d8FallthroughAfter regs global).1 global].
Proof.
  intros Hpc Hnext Hprefix12 Hnil Hdone.
  have HdoneNb := seqStepSourceBlocking _ _ _ _ _ _ Hdone.
  destruct (writeSuccess15694TakeStep _ _ _ Hprefix12
    ltac:(unfold_write_success_101d8_fallthrough_branch; discriminate)
    Hnil HdoneNb) as
    (? & local13 & global13 & ? & prefix13 & Hobs12 & Hstep12 & Hnb13 & Hprefix13).
  eapply writeSuccessCasesCovered in Hstep12.
  2: { unfold_write_success_101d8_fallthrough_branch. reflexivity. }
  destruct Hstep12 as (branch & Hbranch & -> & -> & -> & ->).
  unfold_write_success_101d8_fallthrough_branch.
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
      ltac:(unfold_write_success_101d8_fallthrough; discriminate)
      Hnil HdoneNb) as
      (? & local15 & global15 & ? & prefix15 & Hobs14 & Hstep14 & ? & Hprefix15).
    eapply writeSuccessWriteRegCovered in Hstep14.
    2: reflexivity. 2: exact Hpc. 2: reflexivity. 2: reflexivity.
    destruct Hstep14 as (-> & -> & -> & ->).
    inversion Hprefix15; subst; last contradiction.
    eapply writeSuccessDoneTabledCovered in Hdone.
    2: reflexivity.
    2: { unfold writeSuccess101d8FallthroughRegs. rewrite lookup_insert.
         reflexivity. }
    2: { destruct writeSuccess101d8PcValues as (-> & _). exact Hnext. }
    destruct Hdone as (Hlabels & HafterLocal & HafterGlobal & Hspawned).
    subst labels spawned. destruct after as [afterLocal afterGlobal].
    cbn in HafterLocal, HafterGlobal |- *. subst afterLocal afterGlobal.
    split; first reflexivity.
    unfold writeSuccess101d8FallthroughObservations,
      writeSuccess101d8FallthroughLocals. cbn. reflexivity.
Qed.

Print Assumptions segment_101d8_fallthrough_suffix_covered.
