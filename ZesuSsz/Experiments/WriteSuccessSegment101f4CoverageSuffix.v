Require Import isla.riscv64.riscv64.
Require Import IslaTraces.write_success_02.a101d8.
Require Import IslaTraces.write_success_02.a101f4.
Require Import ZesuSsz.Contracts.InstructionBoundary.
Require Import ZesuSsz.Experiments.WriteSuccessSegmentAutomation.
Require Import ZesuSsz.Experiments.WriteSuccessCoverageAutomation.
Require Import ZesuSsz.Experiments.WriteSuccessSegment15694.
Require Import ZesuSsz.Experiments.WriteSuccessSegment101f4.

Definition writeSuccess101f4TailObservations regs global :=
  skipn 5 (writeSuccess101f4PrefixObservations regs global) ++
  [writeSuccess15694Observation (writeSuccess101f4After regs global).1 global].

Lemma segment_101f4_suffix_covered regs global prefix5 done labels spawned after :
  regs !! "PC" = Some (RVal_Bits (Z_to_bv 64 0x101f4)) ->
  global.(seq_instrs) !! Z_to_bv 64 0x101d8 = Some a101d8 ->
  IslaInstructionPrefixPath
    (writeSuccess15694Local writeSuccess101f4Trace5 regs, global)
    prefix5 done ->
  done.1.(seq_trace) = tnil ->
  seq_step done.1 done.2 labels after.1 after.2 spawned ->
  after = writeSuccess101f4After regs global /\
  prefix5 ++ ({| microLabels := labels; microAfter := after |} :: []) =
    writeSuccess101f4TailObservations regs global.
Proof.
  intros Hpc Hnext Hprefix5 Hnil Hdone.
  have HdoneNb := seqStepSourceBlocking _ _ _ _ _ _ Hdone.
  destruct (writeSuccess15694TakeStep _ _ _ Hprefix5
    ltac:(cbn; discriminate) Hnil HdoneNb) as
    (? & local6 & global6 & ? & prefix6 & Hobs5 & Hstep5 & ? & Hprefix6).
  eapply writeSuccessDefineConstCovered in Hstep5; [|reflexivity|reflexivity].
  destruct Hstep5 as (-> & -> & -> & ->).
  destruct (writeSuccess15694TakeStep _ _ _ Hprefix6
    ltac:(cbn; discriminate) Hnil HdoneNb) as
    (? & local7 & global7 & ? & prefix7 & Hobs6 & Hstep6 & ? & Hprefix7).
  eapply writeSuccessDefineConstCovered in Hstep6; [|reflexivity|reflexivity].
  destruct Hstep6 as (-> & -> & -> & ->).
  destruct (writeSuccess15694TakeStep _ _ _ Hprefix7
    ltac:(cbn; discriminate) Hnil HdoneNb) as
    (? & local8 & global8 & ? & prefix8 & Hobs7 & Hstep7 & ? & Hprefix8).
  eapply writeSuccessDefineConstCovered in Hstep7; [|reflexivity|reflexivity].
  destruct Hstep7 as (-> & -> & -> & ->).
  destruct (writeSuccess15694TakeStep _ _ _ Hprefix8
    ltac:(cbn; discriminate) Hnil HdoneNb) as
    (? & local9 & global9 & ? & prefix9 & Hobs8 & Hstep8 & ? & Hprefix9).
  eapply writeSuccessWriteRegCovered in Hstep8.
  2: reflexivity. 2: exact Hpc. 2: reflexivity. 2: reflexivity.
  destruct Hstep8 as (-> & -> & -> & ->).
  inversion Hprefix9; subst; last contradiction.
  eapply writeSuccessDoneTabledCovered in Hdone.
  2: reflexivity.
  2: { unfold writeSuccess101f4Regs. rewrite lookup_insert. reflexivity. }
  2: exact Hnext.
  destruct Hdone as (Hlabels & HafterLocal & HafterGlobal & Hspawned).
  subst labels spawned. destruct after as [afterLocal afterGlobal].
  cbn in HafterLocal, HafterGlobal |- *. subst afterLocal afterGlobal.
  split; first reflexivity.
  unfold writeSuccess101f4TailObservations,
    writeSuccess101f4PrefixObservations. cbn. reflexivity.
Qed.

Print Assumptions segment_101f4_suffix_covered.
