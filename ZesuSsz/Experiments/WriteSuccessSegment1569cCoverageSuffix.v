From Coq Require Import Eqdep_dec.
Require Import isla.riscv64.riscv64.
Require Import IslaTraces.write_success_90.a1569c.
Require Import IslaTraces.write_success_90.a156a0.
Require Import ZesuSsz.Contracts.InstructionBoundary.
Require Import ZesuSsz.Experiments.WriteSuccessSegmentAutomation.
Require Import ZesuSsz.Experiments.WriteSuccessCoverageAutomation.
Require Import ZesuSsz.Experiments.WriteSuccessSegment15694.
Require Import ZesuSsz.Experiments.WriteSuccessSegment1569cCore.

Definition writeSuccess1569cTailObservations regs global sp :=
  skipn 5 (writeSuccess1569cPrefixObservations regs global sp) ++
  [writeSuccess1569cObservation (writeSuccess1569cAfter regs global sp).1 global].

Lemma segment_1569c_suffix_covered regs global (sp : bv 64) oldX11
    prefix5 done labels spawned after :
  regs !! "PC" = Some (RVal_Bits (Z_to_bv 64 0x1569c)) ->
  regs !! "x8" = Some (RVal_Bits sp) ->
  regs !! "x11" = Some oldX11 ->
  global.(seq_instrs) !! Z_to_bv 64 0x156a0 = Some a156a0 ->
  IslaInstructionPrefixPath
    (writeSuccess1569cLocal writeSuccess1569cTrace5 regs, global)
    prefix5 done ->
  done.1.(seq_trace) = tnil ->
  seq_step done.1 done.2 labels after.1 after.2 spawned ->
  after = writeSuccess1569cAfter regs global sp /\
  prefix5 ++ ({| microLabels := labels; microAfter := after |} :: []) =
    writeSuccess1569cTailObservations regs global sp.
Proof.
  intros Hpc Hsp Hdest Hnext Hprefix5 Hnil Hdone.
  have HdoneNb := seqStepSourceBlocking _ _ _ _ _ _ Hdone.
  destruct (writeSuccess15694TakeStep _ _ _ Hprefix5
    ltac:(cbn; discriminate) Hnil HdoneNb) as
    (? & l6 & g6 & ? & p6 & Ho5 & Hs5 & ? & Hp6).
  pose (b6 := (l6,g6)). inversion Hs5 as [? ? ? ? ? ? ? ? Ht5 Hsem5]; subst.
  unfold b6 in Ht5. cbn [writeSuccess1569cTrace5 writeSuccess1569cTrace4
    writeSuccess1569cTrace3 writeSuccess1569cTrace2 writeSuccess1569cTrace1
    writeSuccess1569cNextPc writeSuccessTraceTail a1569c] in Ht5.
  inversion Ht5; subst. cbn in Hsem5. destruct Hsem5 as (-> & -> & ->).
  destruct (writeSuccess15694TakeStep _ _ _ Hp6
    ltac:(cbn; discriminate) Hnil HdoneNb) as
    (? & l7 & g7 & ? & p7 & Ho6 & Hs6 & Hnb7 & Hp7).
  eapply writeSuccessReadRegCovered in Hs6.
  2: reflexivity. 2: exact Hsp. 2: reflexivity. 2: exact Hnb7.
  destruct Hs6 as (-> & -> & -> & -> & HsymSp).
  cbn in HsymSp. inversion HsymSp as [HspValue].
  match goal with
  | [ Hvalue : existT _ (@BV 64 ?n ?Hwf) = existT _ sp |- _ ] =>
      pose proof (inj_pair2_eq_dec N N.eq_dec (fun width => bv width) 64%N
        (@BV 64 n Hwf) sp Hvalue) as HspBits
  end.
  repeat match goal with H : context [@BV 64 ?n ?Hwf] |- _ =>
    rewrite HspBits in H end.
  destruct (writeSuccess15694TakeStep _ _ _ Hp7
    ltac:(cbn; discriminate) Hnil HdoneNb) as
    (? & l8 & g8 & ? & p8 & Ho7 & Hs7 & ? & Hp8).
  eapply writeSuccessDefineConstCovered in Hs7; [|reflexivity|reflexivity].
  destruct Hs7 as (-> & -> & -> & ->).
  destruct (writeSuccess15694TakeStep _ _ _ Hp8
    ltac:(cbn; discriminate) Hnil HdoneNb) as
    (? & l9 & g9 & ? & p9 & Ho8 & Hs8 & ? & Hp9).
  eapply writeSuccessWriteRegCovered in Hs8.
  2: reflexivity. 2: exact Hdest. 2: reflexivity. 2: reflexivity.
  destruct Hs8 as (-> & -> & -> & ->).
  destruct (writeSuccess15694TakeStep _ _ _ Hp9
    ltac:(cbn; discriminate) Hnil HdoneNb) as
    (? & l10 & g10 & ? & p10 & Ho9 & Hs9 & ? & Hp10).
  eapply writeSuccessWriteRegCovered in Hs9.
  2: reflexivity. 2: rewrite lookup_insert_ne; last done; exact Hpc.
  2: reflexivity. 2: reflexivity.
  destruct Hs9 as (-> & -> & -> & ->).
  inversion Hp10; subst; last contradiction.
  eapply writeSuccessDoneTabledCovered in Hdone.
  2: reflexivity.
  2: { unfold writeSuccess1569cRegs. rewrite lookup_insert. reflexivity. }
  2: { rewrite writeSuccess1569cNextPcExact. exact Hnext. }
  destruct Hdone as (Hlabels & HafterLocal & HafterGlobal & Hspawned).
  subst labels spawned. destruct after as [afterLocal afterGlobal].
  cbn in HafterLocal, HafterGlobal |- *. subst afterLocal afterGlobal.
  split; first reflexivity.
  unfold writeSuccess1569cTailObservations,
    writeSuccess1569cPrefixObservations. cbn. reflexivity.
Qed.

Print Assumptions segment_1569c_suffix_covered.
