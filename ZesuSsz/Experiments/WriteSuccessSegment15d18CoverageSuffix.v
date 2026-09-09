From Coq Require Import Lists.List ZArith.ZArith.
Require Import isla.riscv64.riscv64.
Require Import IslaTraces.write_success_07.a15d1c.
Require Import ZesuSsz.Contracts.InstructionBoundary.
Require Import ZesuSsz.Experiments.WriteSuccessCoverageAutomation.
Require Import ZesuSsz.Experiments.WriteSuccessSegment15694.
Require Import ZesuSsz.Experiments.WriteSuccessSegment15d18.
Require Import ZesuSsz.Experiments.WriteSuccessSegment15d18CoverageSuffixMiddle.
Require Import ZesuSsz.Experiments.WriteSuccessSegment15d18CoverageSuffixFinishBacked.
Require Import ZesuSsz.Experiments.WriteSuccessSegment15d18CoverageSuffixFinishMmio.

Definition writeSuccess15d18SuffixObservations regs global
    (mstatusBits address satp value : bv 64) (result : bool) :=
  [writeSuccess15694Observation
     (writeSuccess15694Local
       (writeSuccess15d18Trace27 mstatusBits address satp value) regs) global;
   writeSuccess15694Observation
     (writeSuccess15694Local
       (writeSuccess15d18Trace28 mstatusBits address satp value) regs) global;
   writeSuccess15694Observation
     (writeSuccess15694Local
       (writeSuccess15d18Trace29 mstatusBits address satp value result) regs) global;
   writeSuccess15694Observation
     (writeSuccess15694Local
       (writeSuccess15d18Trace30 mstatusBits address satp value result) regs)
     (writeSuccess15d18Global global address value);
   writeSuccess15694Observation
     (writeSuccess15694Local
       (writeSuccess15d18Trace31 mstatusBits address satp value result)
       (writeSuccess15d18Regs regs))
     (writeSuccess15d18Global global address value);
   writeSuccess15694Observation
     (writeSuccess15d18After regs global address value).1
     (writeSuccess15d18Global global address value)].

Definition writeSuccess15d18MmioSuffixObservations regs global
    (mstatusBits address satp value : bv 64) (result : bool) :=
  [writeSuccess15694Observation
     (writeSuccess15694Local
       (writeSuccess15d18Trace27 mstatusBits address satp value) regs) global;
   writeSuccess15694Observation
     (writeSuccess15694Local
       (writeSuccess15d18Trace28 mstatusBits address satp value) regs) global;
   writeSuccess15694Observation
     (writeSuccess15694Local
       (writeSuccess15d18Trace29 mstatusBits address satp value result) regs) global;
   {| microLabels :=
        [SWriteMem (writeSuccess15d18Address address) (bv_to_bvn value)];
      microAfter :=
        (writeSuccess15694Local
          (writeSuccess15d18Trace30 mstatusBits address satp value result) regs,
         global) |};
   writeSuccess15694Observation
     (writeSuccess15694Local
       (writeSuccess15d18Trace31 mstatusBits address satp value result)
       (writeSuccess15d18Regs regs)) global;
   writeSuccess15694Observation
     (writeSuccess15d18MmioAfter regs global).1 global].

Lemma segment_15d18_suffix_covered regs global
    (mstatusBits address satp value : bv 64) old
    prefix25 done labels spawned after :
  regs !! "PC" = Some (RVal_Bits (Z_to_bv 64 0x15d18)) ->
  read_mem global.(seq_mem)
    (bv_unsigned (writeSuccess15d18Address address)) 8 = Some old ->
  global.(seq_instrs) !! Z_to_bv 64 0x15d1c = Some a15d1c ->
  IslaInstructionPrefixPath
    (writeSuccess15694Local
      (writeSuccess15d18Trace25 mstatusBits address satp value) regs, global)
    prefix25 done ->
  done.1.(seq_trace) = tnil ->
  seq_step done.1 done.2 labels after.1 after.2 spawned ->
  exists result,
  after = writeSuccess15d18After regs global address value /\
  prefix25 ++ ({| microLabels := labels; microAfter := after |} :: []) =
    writeSuccess15d18SuffixObservations regs global
      mstatusBits address satp value result.
Proof.
  intros Hpc Hmem Hnext Hprefix Hnil Hdone.
  destruct (segment_15d18_suffix_middle_covered regs global mstatusBits
    address satp value prefix25 done labels spawned after Hprefix Hnil Hdone) as
    (result & prefix29 & Hp29 & Hmiddle).
  destruct (segment_15d18_suffix_finish_backed_covered regs global
    mstatusBits address satp value result old prefix29 done labels spawned
    after Hpc Hmem Hnext Hp29 Hnil Hdone) as (Hafter & Hfinish).
  exists result. split; first exact Hafter.
  rewrite Hmiddle. rewrite <- app_assoc. rewrite Hfinish.
  unfold writeSuccess15d18SuffixObservations,
    writeSuccess15d18SuffixMiddleObservations,
    writeSuccess15d18SuffixFinishBackedObservations.
  cbn. reflexivity.

Qed.

Lemma segment_15d18_mmio_suffix_covered regs global
    (mstatusBits address satp value : bv 64) prefix25 done labels spawned after :
  regs !! "PC" = Some (RVal_Bits (Z_to_bv 64 0x15d18)) ->
  read_mem global.(seq_mem)
    (bv_unsigned (writeSuccess15d18Address address)) 8 = None ->
  global.(seq_instrs) !! Z_to_bv 64 0x15d1c = Some a15d1c ->
  IslaInstructionPrefixPath
    (writeSuccess15694Local
      (writeSuccess15d18Trace25 mstatusBits address satp value) regs, global)
    prefix25 done ->
  done.1.(seq_trace) = tnil ->
  seq_step done.1 done.2 labels after.1 after.2 spawned ->
  exists result,
  after = writeSuccess15d18MmioAfter regs global /\
  prefix25 ++ ({| microLabels := labels; microAfter := after |} :: []) =
    writeSuccess15d18MmioSuffixObservations regs global
      mstatusBits address satp value result.
Proof.
  intros Hpc Hmem Hnext Hprefix Hnil Hdone.
  destruct (segment_15d18_suffix_middle_covered regs global mstatusBits
    address satp value prefix25 done labels spawned after Hprefix Hnil Hdone) as
    (result & prefix29 & Hp29 & Hmiddle).
  destruct (segment_15d18_suffix_finish_mmio_covered regs global
    mstatusBits address satp value result prefix29 done labels spawned
    after Hpc Hmem Hnext Hp29 Hnil Hdone) as (Hafter & Hfinish).
  exists result. split; first exact Hafter.
  rewrite Hmiddle. rewrite <- app_assoc. rewrite Hfinish.
  unfold writeSuccess15d18MmioSuffixObservations,
    writeSuccess15d18SuffixMiddleObservations,
    writeSuccess15d18SuffixFinishMmioObservations.
  cbn. reflexivity.

Qed.

Print Assumptions segment_15d18_suffix_covered.
Print Assumptions segment_15d18_mmio_suffix_covered.
