From Coq Require Import Lists.List ZArith.ZArith.
Require Import isla.riscv64.riscv64.
Require Import IslaTraces.write_success_07.a15d18.
Require Import ZesuSsz.Contracts.InstructionBoundary.
Require Import ZesuSsz.Experiments.WriteSuccessCoverageAutomation.
Require Import ZesuSsz.Experiments.WriteSuccessSegment15694.
Require Import ZesuSsz.Experiments.WriteSuccessSegment15d14.
Require Import ZesuSsz.Experiments.WriteSuccessSegment15d14CoverageSuffixMiddle.
Require Import ZesuSsz.Experiments.WriteSuccessSegment15d14CoverageSuffixFinishBacked.
Require Import ZesuSsz.Experiments.WriteSuccessSegment15d14CoverageSuffixFinishMmio.

Definition writeSuccess15d14SuffixObservations regs global
    (mstatusBits address satp value : bv 64) (result : bool) :=
  [writeSuccess15694Observation
     (writeSuccess15694Local
       (writeSuccess15d14Trace27 mstatusBits address satp value) regs) global;
   writeSuccess15694Observation
     (writeSuccess15694Local
       (writeSuccess15d14Trace28 mstatusBits address satp value) regs) global;
   writeSuccess15694Observation
     (writeSuccess15694Local
       (writeSuccess15d14Trace29 mstatusBits address satp value result) regs) global;
   writeSuccess15694Observation
     (writeSuccess15694Local
       (writeSuccess15d14Trace30 mstatusBits address satp value result) regs)
     (writeSuccess15d14Global global address value);
   writeSuccess15694Observation
     (writeSuccess15694Local
       (writeSuccess15d14Trace31 mstatusBits address satp value result)
       (writeSuccess15d14Regs regs))
     (writeSuccess15d14Global global address value);
   writeSuccess15694Observation
     (writeSuccess15d14After regs global address value).1
     (writeSuccess15d14Global global address value)].

Definition writeSuccess15d14MmioSuffixObservations regs global
    (mstatusBits address satp value : bv 64) (result : bool) :=
  [writeSuccess15694Observation
     (writeSuccess15694Local
       (writeSuccess15d14Trace27 mstatusBits address satp value) regs) global;
   writeSuccess15694Observation
     (writeSuccess15694Local
       (writeSuccess15d14Trace28 mstatusBits address satp value) regs) global;
   writeSuccess15694Observation
     (writeSuccess15694Local
       (writeSuccess15d14Trace29 mstatusBits address satp value result) regs) global;
   {| microLabels :=
        [SWriteMem (writeSuccess15d14Address address) (bv_to_bvn value)];
      microAfter :=
        (writeSuccess15694Local
          (writeSuccess15d14Trace30 mstatusBits address satp value result) regs,
         global) |};
   writeSuccess15694Observation
     (writeSuccess15694Local
       (writeSuccess15d14Trace31 mstatusBits address satp value result)
       (writeSuccess15d14Regs regs)) global;
   writeSuccess15694Observation
     (writeSuccess15d14MmioAfter regs global).1 global].

Lemma segment_15d14_suffix_covered regs global
    (mstatusBits address satp value : bv 64) old
    prefix25 done labels spawned after :
  regs !! "PC" = Some (RVal_Bits (Z_to_bv 64 0x15d14)) ->
  read_mem global.(seq_mem)
    (bv_unsigned (writeSuccess15d14Address address)) 8 = Some old ->
  global.(seq_instrs) !! Z_to_bv 64 0x15d18 = Some a15d18 ->
  IslaInstructionPrefixPath
    (writeSuccess15694Local
      (writeSuccess15d14Trace25 mstatusBits address satp value) regs, global)
    prefix25 done ->
  done.1.(seq_trace) = tnil ->
  seq_step done.1 done.2 labels after.1 after.2 spawned ->
  exists result,
  after = writeSuccess15d14After regs global address value /\
  prefix25 ++ ({| microLabels := labels; microAfter := after |} :: []) =
    writeSuccess15d14SuffixObservations regs global
      mstatusBits address satp value result.
Proof.
  intros Hpc Hmem Hnext Hprefix Hnil Hdone.
  destruct (segment_15d14_suffix_middle_covered regs global mstatusBits
    address satp value prefix25 done labels spawned after Hprefix Hnil Hdone) as
    (result & prefix29 & Hp29 & Hmiddle).
  destruct (segment_15d14_suffix_finish_backed_covered regs global
    mstatusBits address satp value result old prefix29 done labels spawned
    after Hpc Hmem Hnext Hp29 Hnil Hdone) as (Hafter & Hfinish).
  exists result. split; first exact Hafter.
  rewrite Hmiddle. rewrite <- app_assoc. rewrite Hfinish.
  unfold writeSuccess15d14SuffixObservations,
    writeSuccess15d14SuffixMiddleObservations,
    writeSuccess15d14SuffixFinishBackedObservations.
  cbn. reflexivity.

Qed.

Lemma segment_15d14_mmio_suffix_covered regs global
    (mstatusBits address satp value : bv 64) prefix25 done labels spawned after :
  regs !! "PC" = Some (RVal_Bits (Z_to_bv 64 0x15d14)) ->
  read_mem global.(seq_mem)
    (bv_unsigned (writeSuccess15d14Address address)) 8 = None ->
  global.(seq_instrs) !! Z_to_bv 64 0x15d18 = Some a15d18 ->
  IslaInstructionPrefixPath
    (writeSuccess15694Local
      (writeSuccess15d14Trace25 mstatusBits address satp value) regs, global)
    prefix25 done ->
  done.1.(seq_trace) = tnil ->
  seq_step done.1 done.2 labels after.1 after.2 spawned ->
  exists result,
  after = writeSuccess15d14MmioAfter regs global /\
  prefix25 ++ ({| microLabels := labels; microAfter := after |} :: []) =
    writeSuccess15d14MmioSuffixObservations regs global
      mstatusBits address satp value result.
Proof.
  intros Hpc Hmem Hnext Hprefix Hnil Hdone.
  destruct (segment_15d14_suffix_middle_covered regs global mstatusBits
    address satp value prefix25 done labels spawned after Hprefix Hnil Hdone) as
    (result & prefix29 & Hp29 & Hmiddle).
  destruct (segment_15d14_suffix_finish_mmio_covered regs global
    mstatusBits address satp value result prefix29 done labels spawned
    after Hpc Hmem Hnext Hp29 Hnil Hdone) as (Hafter & Hfinish).
  exists result. split; first exact Hafter.
  rewrite Hmiddle. rewrite <- app_assoc. rewrite Hfinish.
  unfold writeSuccess15d14MmioSuffixObservations,
    writeSuccess15d14SuffixMiddleObservations,
    writeSuccess15d14SuffixFinishMmioObservations.
  cbn. reflexivity.

Qed.

Print Assumptions segment_15d14_suffix_covered.
Print Assumptions segment_15d14_mmio_suffix_covered.
