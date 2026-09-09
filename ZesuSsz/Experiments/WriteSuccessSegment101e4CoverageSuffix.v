From Coq Require Import Lists.List ZArith.ZArith.
Require Import isla.riscv64.riscv64.
Require Import IslaTraces.write_success_02.a101e8.
Require Import ZesuSsz.Contracts.InstructionBoundary.
Require Import ZesuSsz.Experiments.WriteSuccessSegment15694.
Require Import ZesuSsz.Experiments.WriteSuccessSegment101e4.
Require Import ZesuSsz.Experiments.WriteSuccessSegment101e4CoverageSuffixRead.
Require Import ZesuSsz.Experiments.WriteSuccessSegment101e4CoverageSuffixFinish.

Definition writeSuccess101e4SuffixObservations regs global
    (mstatusBits address satp : bv 64) (byte : bv 8) :=
  [writeSuccess15694Observation
     (writeSuccess15694Local
       (writeSuccess101e4Trace26 mstatusBits address satp byte) regs) global;
   writeSuccess15694Observation
     (writeSuccess15694Local
       (writeSuccess101e4Trace27 mstatusBits address satp byte) regs) global;
   writeSuccess15694Observation
     (writeSuccess15694Local
       (writeSuccess101e4Trace28 mstatusBits address satp byte) regs) global;
   writeSuccess15694Observation
     (writeSuccess15694Local
       (writeSuccess101e4Trace29 mstatusBits address satp byte)
       (<["x13" := RVal_Bits (writeSuccess101e4Loaded byte)]> regs)) global;
   writeSuccess15694Observation
     (writeSuccess15694Local
       (writeSuccess101e4Trace30 mstatusBits address satp byte)
       (writeSuccess101e4Regs regs byte)) global;
   writeSuccess15694Observation (writeSuccess101e4After regs global byte).1 global].

Lemma writeSuccess101e4SuffixObservationsSplit regs global
    (mstatusBits address satp : bv 64) (byte : bv 8) :
  writeSuccess101e4SuffixObservations regs global
      mstatusBits address satp byte =
    writeSuccess101e4SuffixReadObservations regs global
      mstatusBits address satp byte ++
    writeSuccess101e4SuffixFinishObservations regs global
      mstatusBits address satp byte.
Proof. reflexivity. Qed.

Lemma segment_101e4_suffix_covered regs global
    (mstatusBits address satp : bv 64) (byte : bv 8)
    prefix25 done labels spawned after :
  regs !! "PC" = Some (RVal_Bits (Z_to_bv 64 0x101e4)) ->
  regs !! "x13" = Some (RVal_Bits address) ->
  read_mem global.(seq_mem) (bv_unsigned address) 1 = Some (bv_to_bvn byte) ->
  global.(seq_instrs) !! Z_to_bv 64 0x101e8 = Some a101e8 ->
  IslaInstructionPrefixPath
    (writeSuccess15694Local
      (writeSuccess101e4Trace25 mstatusBits address satp) regs, global)
    prefix25 done ->
  done.1.(seq_trace) = tnil ->
  seq_step done.1 done.2 labels after.1 after.2 spawned ->
  after = writeSuccess101e4After regs global byte /\
  prefix25 ++ ({| microLabels := labels; microAfter := after |} :: []) =
    writeSuccess101e4SuffixObservations regs global mstatusBits address satp byte.
Proof.
  intros Hpc Hx13 Hmem Hnext Hprefix Hnil Hdone.
  destruct (segment_101e4_suffix_read_covered regs global
    mstatusBits address satp byte prefix25 done labels spawned after
    Hmem Hprefix Hnil Hdone) as (prefix27 & Hp27 & Hprefix25).
  destruct (segment_101e4_suffix_finish_covered regs global
    mstatusBits address satp byte prefix27 done labels spawned after
    Hpc Hx13 Hnext Hp27 Hnil Hdone) as (Hafter & Hprefix27).
  split; first exact Hafter.
  rewrite Hprefix25. rewrite <- app_assoc. rewrite Hprefix27.
  symmetry. apply writeSuccess101e4SuffixObservationsSplit.
Qed.

Print Assumptions writeSuccess101e4SuffixObservationsSplit.
Print Assumptions segment_101e4_suffix_covered.
