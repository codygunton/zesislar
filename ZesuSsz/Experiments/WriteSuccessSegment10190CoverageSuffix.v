Require Import isla.riscv64.riscv64.
Require Import IslaTraces.write_success_01.a10190.
Require Import IslaTraces.write_success_01.a10194.
Require Import ZesuSsz.Contracts.InstructionBoundary.
Require Import ZesuSsz.Experiments.WriteSuccessSegmentAutomation.
Require Import ZesuSsz.Experiments.WriteSuccessCoverageAutomation.
Require Import ZesuSsz.Experiments.WriteSuccessSegment15694.
Require Import ZesuSsz.Experiments.WriteSuccessSegment10190.

Definition writeSuccess10190TailObservations regs global :=
  skipn 5 (writeSuccess10190PrefixObservations regs global) ++
  [writeSuccess15694Observation (writeSuccess10190After regs global).1 global].

Lemma segment_10190_suffix_covered regs global oldX5
    prefix5 done labels spawned after :
  regs !! "PC" = Some (RVal_Bits (Z_to_bv 64 0x10190)) ->
  regs !! "x5" = Some oldX5 ->
  global.(seq_instrs) !! Z_to_bv 64 0x10194 = Some a10194 ->
  IslaInstructionPrefixPath
    (writeSuccess15694Local writeSuccess10190Trace5 regs, global)
    prefix5 done ->
  done.1.(seq_trace) = tnil ->
  seq_step done.1 done.2 labels after.1 after.2 spawned ->
  after = writeSuccess10190After regs global /\
  prefix5 ++ ({| microLabels := labels; microAfter := after |} :: []) =
    writeSuccess10190TailObservations regs global.
Proof.
  intros Hpc Hdest Hnext Hprefix5 Hnil Hdone.
  have HdoneNb := seqStepSourceBlocking _ _ _ _ _ _ Hdone.
  destruct (writeSuccess15694TakeStep _ _ _ Hprefix5
    ltac:(cbn; discriminate) Hnil HdoneNb) as
    (? & l6 & g6 & ? & p6 & Ho5 & Hs5 & ? & Hp6).
  eapply writeSuccessDefineConstCovered in Hs5; [|reflexivity|reflexivity].
  destruct Hs5 as (-> & -> & -> & ->).
  destruct (writeSuccess15694TakeStep _ _ _ Hp6
    ltac:(cbn; discriminate) Hnil HdoneNb) as
    (? & l7 & g7 & ? & p7 & Ho6 & Hs6 & ? & Hp7).
  eapply writeSuccessWriteRegCovered in Hs6.
  2: reflexivity. 2: exact Hdest. 2: reflexivity. 2: reflexivity.
  destruct Hs6 as (-> & -> & -> & ->).
  destruct (writeSuccess15694TakeStep _ _ _ Hp7
    ltac:(cbn; discriminate) Hnil HdoneNb) as
    (? & l8 & g8 & ? & p8 & Ho7 & Hs7 & ? & Hp8).
  eapply writeSuccessWriteRegCovered in Hs7.
  2: reflexivity. 2: rewrite lookup_insert_ne; last done; exact Hpc.
  2: reflexivity. 2: reflexivity.
  destruct Hs7 as (-> & -> & -> & ->).
  inversion Hp8; subst; last contradiction.
  eapply writeSuccessDoneTabledCovered in Hdone.
  2: reflexivity.
  2: { unfold writeSuccess10190Regs. rewrite lookup_insert. reflexivity. }
  2: { rewrite writeSuccess10190NextPcExact. exact Hnext. }
  destruct Hdone as (Hlabels & HafterLocal & HafterGlobal & Hspawned).
  subst labels spawned. destruct after as [afterLocal afterGlobal].
  cbn in HafterLocal, HafterGlobal |- *. subst afterLocal afterGlobal.
  split; first reflexivity.
  unfold writeSuccess10190TailObservations,
    writeSuccess10190PrefixObservations. cbn. reflexivity.
Qed.

Print Assumptions segment_10190_suffix_covered.
