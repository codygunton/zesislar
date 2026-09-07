Require Import isla.riscv64.riscv64.
Require Import IslaTraces.write_success_07.a15d10.
Require Import ZesuSsz.Contracts.InstructionBoundary.
Require Import ZesuSsz.Experiments.WriteSuccessSegmentAutomation.
Require Import ZesuSsz.Experiments.WriteSuccessCoverageAutomation.
Require Import ZesuSsz.Experiments.WriteSuccessSegment15694.
Require Import ZesuSsz.Experiments.WriteSuccessSegment156b0.

Lemma segment_156b0_suffix_last_covered regs global prefix10 done labels spawned after :
  regs !! "PC" = Some (RVal_Bits (Z_to_bv 64 0x156b0)) ->
  regs !! "x1" = Some (RVal_Bits writeSuccess156b0Ra) ->
  global.(seq_instrs) !! Z_to_bv 64 0x15d10 = Some a15d10 ->
  IslaInstructionPrefixPath
    (writeSuccess15694Local writeSuccess156b0Trace10 regs, global)
    prefix10 done ->
  done.1.(seq_trace) = tnil ->
  seq_step done.1 done.2 labels after.1 after.2 spawned ->
  after = writeSuccess156b0After regs global /\
  prefix10 ++ ({| microLabels := labels; microAfter := after |} :: []) =
    writeSuccess156b0TailLastObservations regs global.
Proof.
  intros Hpc Hx1 Hnext Hprefix10 Hnil Hdone.
  have HdoneNb := seqStepSourceBlocking _ _ _ _ _ _ Hdone.
  destruct (writeSuccess15694TakeStep _ _ _ Hprefix10
    ltac:(cbn; discriminate) Hnil HdoneNb) as
    (? & local11 & global11 & ? & prefix11 & Hobs10 & Hstep10 & ? & Hprefix11).
  eapply writeSuccessWriteRegCovered in Hstep10.
  2: reflexivity. 2: exact Hx1. 2: reflexivity. 2: reflexivity.
  destruct Hstep10 as (-> & -> & -> & ->).
  destruct (writeSuccess15694TakeStep _ _ _ Hprefix11
    ltac:(cbn; discriminate) Hnil HdoneNb) as
    (? & local12 & global12 & ? & prefix12 & Hobs11 & Hstep11 & ? & Hprefix12).
  eapply writeSuccessWriteRegCovered in Hstep11.
  2: reflexivity. 2: rewrite lookup_insert_ne; last done; exact Hpc.
  2: reflexivity. 2: reflexivity.
  destruct Hstep11 as (-> & -> & -> & ->).
  inversion Hprefix12; subst; last contradiction.
  eapply writeSuccessDoneTabledCovered in Hdone.
  2: reflexivity.
  2: { unfold writeSuccess156b0Regs. rewrite lookup_insert. reflexivity. }
  2: { destruct writeSuccess156b0ValuesExact as (_ & _ & _ & Htarget).
       rewrite Htarget. exact Hnext. }
  destruct Hdone as (Hlabels & HafterLocal & HafterGlobal & Hspawned).
  subst labels spawned. destruct after as [afterLocal afterGlobal].
  cbn in HafterLocal, HafterGlobal |- *. subst afterLocal afterGlobal.
  split; first reflexivity.
  unfold writeSuccess156b0TailLastObservations. cbn.
  fold writeSuccess156b0Link writeSuccess156b0TargetMasked.
  reflexivity.
Qed.

Print Assumptions segment_156b0_suffix_last_covered.
