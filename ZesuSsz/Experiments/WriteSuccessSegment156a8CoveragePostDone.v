Require Import isla.riscv64.riscv64.
Require Import IslaTraces.write_success_91.a156ac.
Require Import ZesuSsz.Contracts.InstructionBoundary.
Require Import ZesuSsz.Experiments.WriteSuccessCoverageAutomation.
Require Import ZesuSsz.Experiments.WriteSuccessSegment15694.
Require Import ZesuSsz.Experiments.WriteSuccessSegment156a8.
Lemma segment_156a8_post_done_covered regs global mstatusBits address satp value
    prefix30 done labels spawned after :
  global.(seq_instrs) !! Z_to_bv 64 0x156ac = Some a156ac ->
  IslaInstructionPrefixPath (writeSuccess15694Local
    (writeSuccess156a8Trace30 mstatusBits address satp value)
    (writeSuccess156a8Regs regs value), global) prefix30 done ->
  done.1.(seq_trace) = tnil -> seq_step done.1 done.2 labels after.1 after.2 spawned ->
  after = writeSuccess156a8After regs global value /\
  prefix30 ++ ({| microLabels := labels; microAfter := after |} :: []) =
    [writeSuccess15694Observation (writeSuccess156a8After regs global value).1 global].
Proof.
  intros Hnext Hprefix Hnil Hdone. inversion Hprefix; subst; last contradiction.
  eapply writeSuccessDoneTabledCovered in Hdone.
  2: reflexivity. 2: { unfold writeSuccess156a8Regs. rewrite lookup_insert. reflexivity. }
  2: { rewrite writeSuccess156a8NextPcExact. exact Hnext. }
  destruct Hdone as (-> & Hlocal & Hglobal & ->).
  destruct after as [afterLocal afterGlobal]. cbn in Hlocal, Hglobal |- *.
  subst afterLocal afterGlobal. split; reflexivity.
Qed.
Print Assumptions segment_156a8_post_done_covered.
