(* Generated from the pinned bnez trace shape. *)
(* The renderer validates the pinned operands and endpoints. *)
Require Import isla.riscv64.riscv64.
Require Import IslaTraces.write_success_95.a156e4.
Require Import ZesuSsz.Contracts.InstructionBoundary.
Require Import ZesuSsz.Experiments.WriteSuccessSegmentAutomation.
Require Import ZesuSsz.Experiments.WriteSuccessCoverageAutomation.
Require Import ZesuSsz.Experiments.WriteSuccessSegment15694.
Require Import ZesuSsz.Experiments.WriteSuccessSegment156e4.

Definition writeSuccess156e4First6Observations value condition regs global :=
  firstn 6 (writeSuccess156e4CommonObservations
    value condition regs global).

Ltac unfold_write_success_156e4_prefix H :=
  cbn [writeSuccess156e4Before writeSuccess156e4Trace1
    writeSuccess156e4Trace2 writeSuccess156e4Trace3
    writeSuccess156e4Trace4 writeSuccess156e4Trace5
    writeSuccess156e4Trace6 writeSuccess156e4NextPc
    writeSuccessTraceTail a156e4] in H.

Lemma segment_156e4_prefix6_covered regs global (value : bv 64)
    (condition : bool) observations after :
  regs !! "PC" = Some (RVal_Bits (Z_to_bv 64 0x156e4)) ->
  eval_a_exp regs writeSuccess15694Mstatus = Some (Val_Bool true) ->
  IslaInstructionSegment (writeSuccess156e4Before regs global)
    observations after ->
  exists done labels spawned prefix6,
    IslaInstructionPrefixPath
      (writeSuccess15694Local (writeSuccess156e4Trace6 condition) regs, global)
      prefix6 done /\
    done.1.(seq_trace) = tnil /\
    seq_step done.1 done.2 labels after.1 after.2 spawned /\
    (IslaInstructionBoundary after \/ IslaInstructionTrap after) /\
    observations = writeSuccess156e4First6Observations value condition regs global ++
      prefix6 ++ ({| microLabels := labels; microAfter := after |} :: []).
Proof.
  intros Hpc Hmstatus Hsegment.
  have Halign := writeSuccess156e4AlignmentHolds regs Hpc.
  destruct Hsegment as
    [Hstart done prefix labels spawned Hprefix Hnil Hdone Hobservations Hend].
  have HdoneNb := seqStepSourceBlocking _ _ _ _ _ _ Hdone.
  destruct (writeSuccess15694TakeStep _ _ _ Hprefix
    ltac:(unfold writeSuccess156e4Before, writeSuccess15694Local, a156e4;
      discriminate) Hnil HdoneNb) as
    (? & local1 & global1 & ? & prefix1 & Hobs0 & Hstep0 & ? & Hprefix1).
  pose (before1 := (local1, global1)).
  inversion Hstep0 as [? ? ? ? ? ? ? ? Htrace0 Hsem0]; subst.
  unfold_write_success_156e4_prefix Htrace0. inversion Htrace0; subst.
  cbn in Hsem0. destruct Hsem0 as (-> & -> & ->).
  destruct (writeSuccess15694TakeStep _ _ _ Hprefix1
    ltac:(unfold before1; cbn; discriminate) Hnil HdoneNb) as
    (? & local2 & global2 & ? & prefix2 & Hobs1 & Hstep1 & ? & Hprefix2).
  pose (before2 := (local2, global2)).
  eapply writeSuccessAssumeCovered in Hstep1; [|reflexivity|exact Hmstatus].
  destruct Hstep1 as (-> & -> & -> & ->).
  destruct (writeSuccess15694TakeStep _ _ _ Hprefix2
    ltac:(unfold before2; cbn; discriminate) Hnil HdoneNb) as
    (? & local3 & global3 & ? & prefix3 & Hobs2 & Hstep2 & ? & Hprefix3).
  pose (before3 := (local3, global3)).
  inversion Hstep2 as [? ? ? ? ? ? ? ? Htrace2 Hsem2]; subst.
  unfold before2 in Htrace2. unfold_write_success_156e4_prefix Htrace2.
  inversion Htrace2; subst. cbn in Hsem2. destruct Hsem2 as (-> & -> & ->).
  destruct (writeSuccess15694TakeStep _ _ _ Hprefix3
    ltac:(unfold before3; cbn; discriminate) Hnil HdoneNb) as
    (? & local4 & global4 & ? & prefix4 & Hobs3 & Hstep3 & ? & Hprefix4).
  pose (before4 := (local4, global4)).
  eapply writeSuccessAssumeCovered in Hstep3; [|reflexivity|exact Halign].
  destruct Hstep3 as (-> & -> & -> & ->).
  destruct (writeSuccess15694TakeStep _ _ _ Hprefix4
    ltac:(unfold before4; cbn; discriminate) Hnil HdoneNb) as
    (? & local5 & global5 & ? & prefix5 & Hobs4 & Hstep4 & Hnb5 & Hprefix5).
  eapply writeSuccessReadRegCovered in Hstep4.
  2: reflexivity. 2: exact Hpc. 2: reflexivity. 2: exact Hnb5.
  destruct Hstep4 as (-> & -> & -> & -> & HsymbolicPc).
  cbn in HsymbolicPc. inversion HsymbolicPc as [HpcValue].
  assert (HpcBits : @BV 64 n0 Heq0 = Z_to_bv 64 0x156e4).
  { apply bv_eq. cbn. exact HpcValue. }
  repeat match goal with
  | H : context [@BV 64 n0 Heq0] |- _ => rewrite HpcBits in H
  end.
  destruct (writeSuccess15694TakeStep _ _ _ Hprefix5
    ltac:(cbn; discriminate) Hnil HdoneNb) as
    (? & local6 & global6 & ? & prefix6 & Hobs5 & Hstep5 & ? & Hprefix6).
  eapply writeSuccessDefineConstCovered in Hstep5; [|reflexivity|reflexivity].
  destruct Hstep5 as (-> & -> & -> & ->).
  exists done, labels, spawned, prefix6.
  split; first exact Hprefix6. split; first exact Hnil.
  split; first exact Hdone. split; first exact Hend.
  unfold writeSuccess156e4First6Observations,
    writeSuccess156e4CommonObservations, writeSuccess156e4CommonLocals.
  cbn. rewrite Hobs3. rewrite Hobs4. rewrite Hobs5.
  rewrite HpcBits. reflexivity.
Qed.

Print Assumptions segment_156e4_prefix6_covered.
