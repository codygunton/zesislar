Require Import isla.riscv64.riscv64.
Require Import IslaTraces.write_success_92.a156b8.
Require Import ZesuSsz.Contracts.InstructionBoundary.
Require Import ZesuSsz.Experiments.WriteSuccessCoverageAutomation.
Require Import ZesuSsz.Experiments.WriteSuccessSegment15694.
Require Import ZesuSsz.Experiments.WriteSuccessSegment156b4.
Lemma segment_156b4_post_done_covered regs global mstatusBits address satp value
    prefix30 done labels spawned after :
  global.(seq_instrs) !! Z_to_bv 64 0x156b8 = Some a156b8 ->
  IslaInstructionPrefixPath (writeSuccess15694Local
    (writeSuccess156b4Trace30 mstatusBits address satp value)
    (writeSuccess156b4Regs regs value), global) prefix30 done ->
  done.1.(seq_trace) = tnil -> seq_step done.1 done.2 labels after.1 after.2 spawned ->
  after = writeSuccess156b4After regs global value /\
  prefix30 ++ ({| microLabels := labels; microAfter := after |} :: []) =
    [writeSuccess15694Observation (writeSuccess156b4After regs global value).1 global].
Proof.
  intros Hnext Hprefix Hnil Hdone. inversion Hprefix; subst; last contradiction.
  eapply writeSuccessDoneTabledCovered in Hdone.
  2: reflexivity. 2: { unfold writeSuccess156b4Regs. rewrite lookup_insert. reflexivity. }
  2: { rewrite writeSuccess156b4NextPcExact. exact Hnext. }
  destruct Hdone as (-> & Hlocal & Hglobal & ->).
  destruct after as [afterLocal afterGlobal]. cbn in Hlocal, Hglobal |- *.
  subst afterLocal afterGlobal. split; reflexivity.
Qed.
Print Assumptions segment_156b4_post_done_covered.
