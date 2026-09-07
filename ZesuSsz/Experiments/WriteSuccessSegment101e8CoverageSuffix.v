From Coq Require Import Eqdep_dec.
Require Import isla.riscv64.riscv64.
Require Import IslaTraces.write_success_02.a101e8.
Require Import IslaTraces.write_success_02.a101ec.
Require Import ZesuSsz.Contracts.InstructionBoundary.
Require Import ZesuSsz.Experiments.WriteSuccessSegmentAutomation.
Require Import ZesuSsz.Experiments.WriteSuccessCoverageAutomation.
Require Import ZesuSsz.Experiments.WriteSuccessSegment15694.
Require Import ZesuSsz.Experiments.WriteSuccessSegment101e8.

Definition writeSuccess101e8TailObservations regs global left right :=
  skipn 7 (writeSuccess101e8PrefixObservations regs global left right) ++
  [writeSuccess15694Observation
    (writeSuccess101e8After regs global left right).1 global].

Lemma segment_101e8_suffix_covered regs global (left right : bv 64) oldX14
    prefix7 done labels spawned after :
  regs !! "PC" = Some (RVal_Bits (Z_to_bv 64 0x101e8)) ->
  regs !! "x15" = Some (RVal_Bits right) ->
  regs !! "x14" = Some oldX14 ->
  global.(seq_instrs) !! Z_to_bv 64 0x101ec = Some a101ec ->
  IslaInstructionPrefixPath
    (writeSuccess15694Local (writeSuccess101e8Trace7 left) regs, global)
    prefix7 done ->
  done.1.(seq_trace) = tnil ->
  seq_step done.1 done.2 labels after.1 after.2 spawned ->
  after = writeSuccess101e8After regs global left right /\
  prefix7 ++ ({| microLabels := labels; microAfter := after |} :: []) =
    writeSuccess101e8TailObservations regs global left right.
Proof.
  intros Hpc Hright Hdest Hnext Hprefix7 Hnil Hdone.
  have HdoneNb := seqStepSourceBlocking _ _ _ _ _ _ Hdone.
  destruct (writeSuccess15694TakeStep _ _ _ Hprefix7
    ltac:(cbn; discriminate) Hnil HdoneNb) as
    (? & local8 & global8 & ? & prefix8 & Hobs7 & Hstep7 & ? & Hprefix8).
  pose (before8 := (local8, global8)).
  inversion Hstep7 as [? ? ? ? ? ? ? ? Htrace7 Hsem7]; subst.
  unfold before8 in Htrace7. cbn [writeSuccess101e8Trace7
    writeSuccess101e8Trace6 writeSuccess101e8Trace5
    writeSuccess101e8Trace4 writeSuccess101e8Trace3
    writeSuccess101e8Trace2 writeSuccess101e8Trace1
    writeSuccess101e8NextPc writeSuccessTraceTail a101e8] in Htrace7.
  inversion Htrace7; subst. cbn in Hsem7. destruct Hsem7 as (-> & -> & ->).
  destruct (writeSuccess15694TakeStep _ _ _ Hprefix8
    ltac:(cbn; discriminate) Hnil HdoneNb) as
    (? & local9 & global9 & ? & prefix9 & Hobs8 & Hstep8 & Hnb9 & Hprefix9).
  eapply writeSuccessReadRegCovered in Hstep8.
  2: reflexivity. 2: exact Hright. 2: reflexivity. 2: exact Hnb9.
  destruct Hstep8 as (-> & -> & -> & -> & HsymbolicRight).
  cbn in HsymbolicRight. inversion HsymbolicRight as [HrightValue].
  match goal with
  | [ Hvalue : existT _ (@BV 64 ?n ?Hwf) = existT _ right |- _ ] =>
      pose proof (inj_pair2_eq_dec N N.eq_dec (fun width => bv width) 64%N
        (@BV 64 n Hwf) right Hvalue) as HrightBits
  end.
  repeat match goal with
  | H : context [@BV 64 ?n ?Hwf] |- _ => rewrite HrightBits in H
  end.
  destruct (writeSuccess15694TakeStep _ _ _ Hprefix9
    ltac:(cbn; discriminate) Hnil HdoneNb) as
    (? & local10 & global10 & ? & prefix10 & Hobs9 & Hstep9 & ? & Hprefix10).
  eapply writeSuccessDefineConstCovered in Hstep9; [|reflexivity|reflexivity].
  destruct Hstep9 as (-> & -> & -> & ->).
  destruct (writeSuccess15694TakeStep _ _ _ Hprefix10
    ltac:(cbn; discriminate) Hnil HdoneNb) as
    (? & local11 & global11 & ? & prefix11 & Hobs10 & Hstep10 & ? & Hprefix11).
  eapply writeSuccessWriteRegCovered in Hstep10.
  2: reflexivity. 2: exact Hdest. 2: reflexivity. 2: reflexivity.
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
  2: { unfold writeSuccess101e8Regs. rewrite lookup_insert. reflexivity. }
  2: { rewrite writeSuccess101e8NextPcExact. exact Hnext. }
  destruct Hdone as (Hlabels & HafterLocal & HafterGlobal & Hspawned).
  subst labels spawned. destruct after as [afterLocal afterGlobal].
  cbn in HafterLocal, HafterGlobal |- *. subst afterLocal afterGlobal.
  split; first reflexivity.
  unfold writeSuccess101e8TailObservations,
    writeSuccess101e8PrefixObservations, writeSuccess101e8Locals. cbn.
  reflexivity.
Qed.

Print Assumptions segment_101e8_suffix_covered.
