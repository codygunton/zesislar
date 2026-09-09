Require Import isla.riscv64.riscv64.
Require Import IslaTraces.write_success_07.a15d30.
Require Import ZesuSsz.Contracts.InstructionBoundary.
Require Import ZesuSsz.Experiments.WriteSuccessSegment15694.
Require Import ZesuSsz.Experiments.WriteSuccessSegment15d2c.
Require Import ZesuSsz.Experiments.WriteSuccessSegment15d2cCoverageSuffixFirst.
Require Import ZesuSsz.Experiments.WriteSuccessSegment15d2cCoverageReadBacked.
Require Import ZesuSsz.Experiments.WriteSuccessSegment15d2cCoverageReadMmio.
Require Import ZesuSsz.Experiments.WriteSuccessSegment15d2cCoveragePostSign.
Require Import ZesuSsz.Experiments.WriteSuccessSegment15d2cCoveragePostDest.
Require Import ZesuSsz.Experiments.WriteSuccessSegment15d2cCoveragePostPc.
Require Import ZesuSsz.Experiments.WriteSuccessSegment15d2cCoveragePostDone.

Definition writeSuccess15d2cSuffixObservations regs global
    (mstatusBits address satp value : bv 64) (readLabels : list seq_label) :=
  writeSuccess15d2cSuffixFirstObservations regs global mstatusBits address satp value ++
  ({| microLabels := readLabels; microAfter := (writeSuccess15694Local
      (writeSuccess15d2cTrace27 mstatusBits address satp value) regs, global) |} ::
   writeSuccess15d2cPostReadPrefix regs global mstatusBits address satp value) ++
  [writeSuccess15694Observation (writeSuccess15d2cAfter regs global value).1 global].

Lemma segment_15d2c_suffix_backed_covered regs global
    (mstatusBits address satp value oldDest : bv 64)
    prefix21 done labels spawned after :
  regs !! "PC" = Some (RVal_Bits (Z_to_bv 64 0x15d2c)) ->
  regs !! "satp" = Some (RVal_Bits satp) ->
  regs !! "x1" = Some (RVal_Bits oldDest) ->
  read_mem global.(seq_mem) (bv_unsigned (writeSuccess15d2cAddress address)) 8 =
    Some (bv_to_bvn value) ->
  global.(seq_instrs) !! Z_to_bv 64 0x15d30 = Some a15d30 ->
  IslaInstructionPrefixPath (writeSuccess15694Local
    (writeSuccess15d2cTrace21 mstatusBits address) regs, global) prefix21 done ->
  done.1.(seq_trace) = tnil -> seq_step done.1 done.2 labels after.1 after.2 spawned ->
  after = writeSuccess15d2cAfter regs global value /\
  prefix21 ++ ({| microLabels := labels; microAfter := after |} :: []) =
    writeSuccess15d2cSuffixObservations regs global mstatusBits address satp value [].
Proof.
  intros Hpc Hsatp Hdest Hmem Hnext Hp21 Hnil Hdone.
  destruct (segment_15d2c_suffix_first_covered regs global mstatusBits address satp
    prefix21 done labels spawned after Hsatp Hp21 Hnil Hdone) as (decl & p26 & Hp26 & Ho1).
  destruct (segment_15d2c_read_backed_covered regs global mstatusBits address satp
    decl value p26 done labels spawned after Hmem Hp26 Hnil Hdone) as (-> & p27 & Hp27 & Ho2).
  destruct (segment_15d2c_post_sign_covered regs global mstatusBits address satp value
    p27 done labels spawned after Hp27 Hnil Hdone) as (p28 & Hp28 & Ho3).
  destruct (segment_15d2c_post_dest_covered regs global mstatusBits address satp value
    oldDest p28 done labels spawned after Hdest Hp28 Hnil Hdone) as (p29 & Hp29 & Ho4).
  destruct (segment_15d2c_post_pc_covered regs global mstatusBits address satp value
    p29 done labels spawned after Hpc Hp29 Hnil Hdone) as (p30 & Hp30 & Ho5).
  destruct (segment_15d2c_post_done_covered regs global mstatusBits address satp value
    p30 done labels spawned after Hnext Hp30 Hnil Hdone) as (Hafter & Ho6).
  split; first exact Hafter. rewrite Ho1. rewrite Ho2. rewrite Ho3. rewrite Ho4. rewrite Ho5.
  repeat rewrite <- app_assoc. cbn [List.app]. rewrite Ho6.
  unfold writeSuccess15d2cSuffixObservations,
    writeSuccess15d2cPostReadPrefix. cbn. reflexivity.
Qed.

Lemma segment_15d2c_suffix_mmio_covered regs global
    (mstatusBits address satp oldDest : bv 64)
    prefix21 done labels spawned after :
  regs !! "PC" = Some (RVal_Bits (Z_to_bv 64 0x15d2c)) ->
  regs !! "satp" = Some (RVal_Bits satp) ->
  regs !! "x1" = Some (RVal_Bits oldDest) ->
  read_mem global.(seq_mem) (bv_unsigned (writeSuccess15d2cAddress address)) 8 = None ->
  global.(seq_instrs) !! Z_to_bv 64 0x15d30 = Some a15d30 ->
  IslaInstructionPrefixPath (writeSuccess15694Local
    (writeSuccess15d2cTrace21 mstatusBits address) regs, global) prefix21 done ->
  done.1.(seq_trace) = tnil -> seq_step done.1 done.2 labels after.1 after.2 spawned ->
  exists value, after = writeSuccess15d2cAfter regs global value /\
  prefix21 ++ ({| microLabels := labels; microAfter := after |} :: []) =
    writeSuccess15d2cSuffixObservations regs global mstatusBits address satp value
      [SReadMem (writeSuccess15d2cAddress address) (bv_to_bvn value)].
Proof.
  intros Hpc Hsatp Hdest Hmem Hnext Hp21 Hnil Hdone.
  destruct (segment_15d2c_suffix_first_covered regs global mstatusBits address satp
    prefix21 done labels spawned after Hsatp Hp21 Hnil Hdone) as (value & p26 & Hp26 & Ho1).
  destruct (segment_15d2c_read_mmio_covered regs global mstatusBits address satp
    value p26 done labels spawned after Hmem Hp26 Hnil Hdone) as (p27 & Hp27 & Ho2).
  destruct (segment_15d2c_post_sign_covered regs global mstatusBits address satp value
    p27 done labels spawned after Hp27 Hnil Hdone) as (p28 & Hp28 & Ho3).
  destruct (segment_15d2c_post_dest_covered regs global mstatusBits address satp value
    oldDest p28 done labels spawned after Hdest Hp28 Hnil Hdone) as (p29 & Hp29 & Ho4).
  destruct (segment_15d2c_post_pc_covered regs global mstatusBits address satp value
    p29 done labels spawned after Hpc Hp29 Hnil Hdone) as (p30 & Hp30 & Ho5).
  destruct (segment_15d2c_post_done_covered regs global mstatusBits address satp value
    p30 done labels spawned after Hnext Hp30 Hnil Hdone) as (Hafter & Ho6).
  exists value. split; first exact Hafter. rewrite Ho1. rewrite Ho2. rewrite Ho3. rewrite Ho4. rewrite Ho5.
  repeat rewrite <- app_assoc. cbn [List.app]. rewrite Ho6.
  unfold writeSuccess15d2cSuffixObservations,
    writeSuccess15d2cPostReadPrefix. cbn. reflexivity.
Qed.
Print Assumptions segment_15d2c_suffix_backed_covered.
Print Assumptions segment_15d2c_suffix_mmio_covered.
