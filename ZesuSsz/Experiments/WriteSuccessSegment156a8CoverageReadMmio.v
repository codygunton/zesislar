Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Contracts.InstructionBoundary.
Require Import ZesuSsz.Experiments.WriteSuccessCoverageAutomation.
Require Import ZesuSsz.Experiments.WriteSuccessSegment15694.
Require Import ZesuSsz.Experiments.WriteSuccessSegment156a8.
Require Import ZesuSsz.Experiments.WriteSuccessSegment156a8ReadCoverage.

Lemma segment_156a8_read_mmio_covered regs global mstatusBits address satp
    value prefix26 done labels spawned after :
  read_mem global.(seq_mem) (bv_unsigned (writeSuccess156a8Address address)) 8 = None ->
  IslaInstructionPrefixPath (writeSuccess15694Local
    (writeSuccess156a8Trace26 mstatusBits address satp value) regs, global)
    prefix26 done -> done.1.(seq_trace) = tnil ->
  seq_step done.1 done.2 labels after.1 after.2 spawned ->
  exists prefix27,
  IslaInstructionPrefixPath (writeSuccess15694Local
    (writeSuccess156a8Trace27 mstatusBits address satp value) regs, global)
    prefix27 done /\
  prefix26 = {| microLabels := [SReadMem (writeSuccess156a8Address address) (bv_to_bvn value)];
    microAfter := (writeSuccess15694Local
      (writeSuccess156a8Trace27 mstatusBits address satp value) regs, global) |} :: prefix27.
Proof.
  intros Hmem Hprefix Hnil Hdone. have HdoneNb := seqStepSourceBlocking _ _ _ _ _ _ Hdone.
  destruct (writeSuccess15694TakeStep _ _ _ Hprefix ltac:(cbn; discriminate) Hnil HdoneNb)
    as (? & l27 & g27 & ? & p27 & Ho26 & Hs26 & ? & Hp27).
  eapply writeSuccess156a8ReadMmioValueCovered in Hs26.
  2: reflexivity. 2: exact Hmem.
  destruct Hs26 as (-> & -> & -> & ->).
  exists p27. split; first exact Hp27. rewrite Ho26. reflexivity.
Qed.
Print Assumptions segment_156a8_read_mmio_covered.
