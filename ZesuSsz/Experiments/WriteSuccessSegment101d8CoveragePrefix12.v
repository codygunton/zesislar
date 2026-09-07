From Coq Require Import Eqdep_dec.
Require Import isla.riscv64.riscv64.
Require Import IslaTraces.write_success_02.a101d8.
Require Import ZesuSsz.Contracts.InstructionBoundary.
Require Import ZesuSsz.Experiments.WriteSuccessSegmentAutomation.
Require Import ZesuSsz.Experiments.WriteSuccessCoverageAutomation.
Require Import ZesuSsz.Experiments.WriteSuccessSegment15694.
Require Import ZesuSsz.Experiments.WriteSuccessSegment101d8.

Definition writeSuccess101d8Second6Observations left right condition regs global :=
  skipn 6 (writeSuccess101d8CommonObservations left right condition regs global).

Lemma segment_101d8_prefix12_covered regs global (left right : bv 64)
    (condition : bool) prefix6 done :
  regs !! "x15" = Some (RVal_Bits left) ->
  regs !! "x12" = Some (RVal_Bits right) ->
  eval_exp (writeSuccess101d8Condition left right) = Some (Val_Bool condition) ->
  IslaInstructionPrefixPath
    (writeSuccess15694Local (writeSuccess101d8Trace6 condition) regs, global)
    prefix6 done ->
  done.1.(seq_trace) = tnil ->
  done.1.(seq_nb_state) = false ->
  exists prefix12,
    IslaInstructionPrefixPath
      (writeSuccess15694Local
        (writeSuccess101d8Trace12 left right condition) regs, global)
      prefix12 done /\
    prefix6 = writeSuccess101d8Second6Observations
      left right condition regs global ++ prefix12.
Proof.
  intros Hx15 Hx12 Hcondition Hprefix6 Hnil HdoneNb.
  destruct (writeSuccess15694TakeStep _ _ _ Hprefix6
    ltac:(cbn; discriminate) Hnil HdoneNb) as
    (? & local7 & global7 & ? & prefix7 & Hobs6 & Hstep6 & ? & Hprefix7).
  pose (before7 := (local7, global7)).
  inversion Hstep6 as [? ? ? ? ? ? ? ? Htrace6 Hsem6]; subst.
  cbn [writeSuccess101d8Trace6 writeSuccess101d8Trace5
    writeSuccess101d8Trace4 writeSuccess101d8Trace3
    writeSuccess101d8Trace2 writeSuccess101d8Trace1
    writeSuccess101d8NextPc writeSuccessTraceTail a101d8] in Htrace6.
  inversion Htrace6; subst. cbn in Hsem6. destruct Hsem6 as (-> & -> & ->).
  destruct (writeSuccess15694TakeStep _ _ _ Hprefix7
    ltac:(unfold before7; cbn; discriminate) Hnil HdoneNb) as
    (? & local8 & global8 & ? & prefix8 & Hobs7 & Hstep7 & Hnb8 & Hprefix8).
  eapply writeSuccessReadRegCovered in Hstep7.
  2: reflexivity. 2: exact Hx15. 2: reflexivity. 2: exact Hnb8.
  destruct Hstep7 as (-> & -> & -> & -> & HsymbolicLeft).
  cbn in HsymbolicLeft. inversion HsymbolicLeft as [HleftValue].
  pose proof (inj_pair2_eq_dec N (Coq.NArith.BinNat.N.eq_dec)
    (fun width => bv width) 64%N (@BV 64 n Heq) left HleftValue)
    as HleftBits.
  repeat match goal with
  | H : context [@BV 64 n Heq] |- _ => rewrite HleftBits in H
  end.
  destruct (writeSuccess15694TakeStep _ _ _ Hprefix8
    ltac:(cbn; discriminate) Hnil HdoneNb) as
    (? & local9 & global9 & ? & prefix9 & Hobs8 & Hstep8 & ? & Hprefix9).
  pose (before9 := (local9, global9)).
  inversion Hstep8 as [? ? ? ? ? ? ? ? Htrace8 Hsem8]; subst.
  unfold before9 in Htrace8. cbn in Htrace8. inversion Htrace8; subst.
  cbn in Hsem8. destruct Hsem8 as (-> & -> & ->).
  destruct (writeSuccess15694TakeStep _ _ _ Hprefix9
    ltac:(cbn; discriminate) Hnil HdoneNb) as
    (? & local10 & global10 & ? & prefix10 & Hobs9 & Hstep9 & Hnb10 & Hprefix10).
  eapply writeSuccessReadRegCovered in Hstep9.
  2: reflexivity. 2: exact Hx12. 2: reflexivity. 2: exact Hnb10.
  destruct Hstep9 as (-> & -> & -> & -> & HsymbolicRight).
  cbn in HsymbolicRight. inversion HsymbolicRight as [HrightValue].
  pose proof (inj_pair2_eq_dec N (Coq.NArith.BinNat.N.eq_dec)
    (fun width => bv width) 64%N (@BV 64 n0 Heq0) right HrightValue)
    as HrightBits.
  repeat match goal with
  | H : context [@BV 64 n0 Heq0] |- _ => rewrite HrightBits in H
  end.
  destruct (writeSuccess15694TakeStep _ _ _ Hprefix10
    ltac:(cbn; discriminate) Hnil HdoneNb) as
    (? & local11 & global11 & ? & prefix11 & Hobs10 & Hstep10 & ? & Hprefix11).
  rename Hobs10 into HobsCondition.
  eapply writeSuccessDefineConstCovered in Hstep10; [|reflexivity|exact Hcondition].
  destruct Hstep10 as (-> & -> & -> & ->).
  destruct (writeSuccess15694TakeStep _ _ _ Hprefix11
    ltac:(cbn; discriminate) Hnil HdoneNb) as
    (? & local12 & global12 & ? & prefix12 & Hobs11 & Hstep11 & ? & Hprefix12).
  rename Hobs11 into HobsTarget.
  eapply writeSuccessDefineConstCovered in Hstep11; [|reflexivity|reflexivity].
  destruct Hstep11 as (-> & -> & -> & ->).
  exists prefix12. split; first exact Hprefix12.
  unfold writeSuccess101d8Second6Observations,
    writeSuccess101d8CommonObservations, writeSuccess101d8CommonLocals.
  cbn. rewrite Hobs9. rewrite HobsCondition. rewrite HobsTarget.
  rewrite HrightBits. reflexivity.
Qed.

Print Assumptions segment_101d8_prefix12_covered.
