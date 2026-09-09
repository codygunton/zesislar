Require Import isla.riscv64.riscv64.
Require Import IslaTraces.write_success_94.a156d4.
Require Import ZesuSsz.Contracts.InstructionBoundary.
Require Import ZesuSsz.Experiments.WriteSuccessSegment15694.
Require Import ZesuSsz.Experiments.WriteSuccessSegment156d0.
Require Import ZesuSsz.Experiments.WriteSuccessSegment156d0CoverageSuffixFirst.
Require Import ZesuSsz.Experiments.WriteSuccessSegment156d0CoverageReadBacked.
Require Import ZesuSsz.Experiments.WriteSuccessSegment156d0CoverageReadMmio.
Require Import ZesuSsz.Experiments.WriteSuccessSegment156d0CoveragePostSign.
Require Import ZesuSsz.Experiments.WriteSuccessSegment156d0CoveragePostDest.
Require Import ZesuSsz.Experiments.WriteSuccessSegment156d0CoveragePostPc.
Require Import ZesuSsz.Experiments.WriteSuccessSegment156d0CoveragePostDone.

Definition writeSuccess156d0SuffixObservations regs global
    (mstatusBits address satp value : bv 64) (readLabels : list seq_label) :=
  writeSuccess156d0SuffixFirstObservations regs global mstatusBits address satp value ++
  ({| microLabels := readLabels; microAfter := (writeSuccess15694Local
      (writeSuccess156d0Trace27 mstatusBits address satp value) regs, global) |} ::
   writeSuccess156d0PostReadPrefix regs global mstatusBits address satp value) ++
  [writeSuccess15694Observation (writeSuccess156d0After regs global value).1 global].

Lemma segment_156d0_suffix_backed_covered regs global
    (mstatusBits address satp value oldDest : bv 64)
    prefix21 done labels spawned after :
  regs !! "PC" = Some (RVal_Bits (Z_to_bv 64 0x156d0)) ->
  regs !! "satp" = Some (RVal_Bits satp) ->
  regs !! "x10" = Some (RVal_Bits oldDest) ->
  read_mem global.(seq_mem) (bv_unsigned (writeSuccess156d0Address address)) 8 =
    Some (bv_to_bvn value) ->
  global.(seq_instrs) !! Z_to_bv 64 0x156d4 = Some a156d4 ->
  IslaInstructionPrefixPath (writeSuccess15694Local
    (writeSuccess156d0Trace21 mstatusBits address) regs, global) prefix21 done ->
  done.1.(seq_trace) = tnil -> seq_step done.1 done.2 labels after.1 after.2 spawned ->
  after = writeSuccess156d0After regs global value /\
  prefix21 ++ ({| microLabels := labels; microAfter := after |} :: []) =
    writeSuccess156d0SuffixObservations regs global mstatusBits address satp value [].
Proof.
  intros Hpc Hsatp Hdest Hmem Hnext Hp21 Hnil Hdone.
  destruct (segment_156d0_suffix_first_covered regs global mstatusBits address satp
    prefix21 done labels spawned after Hsatp Hp21 Hnil Hdone) as (decl & p26 & Hp26 & Ho1).
  destruct (segment_156d0_read_backed_covered regs global mstatusBits address satp
    decl value p26 done labels spawned after Hmem Hp26 Hnil Hdone) as (-> & p27 & Hp27 & Ho2).
  destruct (segment_156d0_post_sign_covered regs global mstatusBits address satp value
    p27 done labels spawned after Hp27 Hnil Hdone) as (p28 & Hp28 & Ho3).
  destruct (segment_156d0_post_dest_covered regs global mstatusBits address satp value
    oldDest p28 done labels spawned after Hdest Hp28 Hnil Hdone) as (p29 & Hp29 & Ho4).
  destruct (segment_156d0_post_pc_covered regs global mstatusBits address satp value
    p29 done labels spawned after Hpc Hp29 Hnil Hdone) as (p30 & Hp30 & Ho5).
  destruct (segment_156d0_post_done_covered regs global mstatusBits address satp value
    p30 done labels spawned after Hnext Hp30 Hnil Hdone) as (Hafter & Ho6).
  split; first exact Hafter. rewrite Ho1. rewrite Ho2. rewrite Ho3. rewrite Ho4. rewrite Ho5.
  repeat rewrite <- app_assoc. cbn [List.app]. rewrite Ho6.
  unfold writeSuccess156d0SuffixObservations,
    writeSuccess156d0PostReadPrefix. cbn. reflexivity.
Qed.

Lemma segment_156d0_suffix_mmio_covered regs global
    (mstatusBits address satp oldDest : bv 64)
    prefix21 done labels spawned after :
  regs !! "PC" = Some (RVal_Bits (Z_to_bv 64 0x156d0)) ->
  regs !! "satp" = Some (RVal_Bits satp) ->
  regs !! "x10" = Some (RVal_Bits oldDest) ->
  read_mem global.(seq_mem) (bv_unsigned (writeSuccess156d0Address address)) 8 = None ->
  global.(seq_instrs) !! Z_to_bv 64 0x156d4 = Some a156d4 ->
  IslaInstructionPrefixPath (writeSuccess15694Local
    (writeSuccess156d0Trace21 mstatusBits address) regs, global) prefix21 done ->
  done.1.(seq_trace) = tnil -> seq_step done.1 done.2 labels after.1 after.2 spawned ->
  exists value, after = writeSuccess156d0After regs global value /\
  prefix21 ++ ({| microLabels := labels; microAfter := after |} :: []) =
    writeSuccess156d0SuffixObservations regs global mstatusBits address satp value
      [SReadMem (writeSuccess156d0Address address) (bv_to_bvn value)].
Proof.
  intros Hpc Hsatp Hdest Hmem Hnext Hp21 Hnil Hdone.
  destruct (segment_156d0_suffix_first_covered regs global mstatusBits address satp
    prefix21 done labels spawned after Hsatp Hp21 Hnil Hdone) as (value & p26 & Hp26 & Ho1).
  destruct (segment_156d0_read_mmio_covered regs global mstatusBits address satp
    value p26 done labels spawned after Hmem Hp26 Hnil Hdone) as (p27 & Hp27 & Ho2).
  destruct (segment_156d0_post_sign_covered regs global mstatusBits address satp value
    p27 done labels spawned after Hp27 Hnil Hdone) as (p28 & Hp28 & Ho3).
  destruct (segment_156d0_post_dest_covered regs global mstatusBits address satp value
    oldDest p28 done labels spawned after Hdest Hp28 Hnil Hdone) as (p29 & Hp29 & Ho4).
  destruct (segment_156d0_post_pc_covered regs global mstatusBits address satp value
    p29 done labels spawned after Hpc Hp29 Hnil Hdone) as (p30 & Hp30 & Ho5).
  destruct (segment_156d0_post_done_covered regs global mstatusBits address satp value
    p30 done labels spawned after Hnext Hp30 Hnil Hdone) as (Hafter & Ho6).
  exists value. split; first exact Hafter. rewrite Ho1. rewrite Ho2. rewrite Ho3. rewrite Ho4. rewrite Ho5.
  repeat rewrite <- app_assoc. cbn [List.app]. rewrite Ho6.
  unfold writeSuccess156d0SuffixObservations,
    writeSuccess156d0PostReadPrefix. cbn. reflexivity.
Qed.
Print Assumptions segment_156d0_suffix_backed_covered.
Print Assumptions segment_156d0_suffix_mmio_covered.
