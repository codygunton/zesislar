From Coq Require Import Eqdep_dec Lists.List ZArith.ZArith.
Require Import isla.riscv64.riscv64.
Require Import IslaTraces.write_success_02.a101e8.
Require Import ZesuSsz.Contracts.InstructionBoundary.
Require Import ZesuSsz.Experiments.WriteSuccessCoverageAutomation.
Require Import ZesuSsz.Experiments.WriteSuccessSegment15694.
Require Import ZesuSsz.Experiments.WriteSuccessSegment101e4.

Definition writeSuccess101e4SuffixFinishObservations regs global
    (mstatusBits address satp : bv 64) (byte : bv 8) :=
  [writeSuccess15694Observation
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
   writeSuccess15694Observation
     (writeSuccess101e4After regs global byte).1 global].

Lemma segment_101e4_suffix_finish_covered regs global
    (mstatusBits address satp : bv 64) (byte : bv 8)
    prefix27 done labels spawned after :
  regs !! "PC" = Some (RVal_Bits (Z_to_bv 64 0x101e4)) ->
  regs !! "x13" = Some (RVal_Bits address) ->
  global.(seq_instrs) !! Z_to_bv 64 0x101e8 = Some a101e8 ->
  IslaInstructionPrefixPath
    (writeSuccess15694Local
      (writeSuccess101e4Trace27 mstatusBits address satp byte) regs,
      global) prefix27 done ->
  done.1.(seq_trace) = tnil ->
  seq_step done.1 done.2 labels after.1 after.2 spawned ->
  after = writeSuccess101e4After regs global byte /\
  prefix27 ++ ({| microLabels := labels; microAfter := after |} :: []) =
    writeSuccess101e4SuffixFinishObservations regs global
      mstatusBits address satp byte.
Proof.
  intros Hpc Hx13 Hnext Hprefix Hnil Hdone.
  have HdoneNb := seqStepSourceBlocking _ _ _ _ _ _ Hdone.
  destruct (writeSuccess15694TakeStep _ _ _ Hprefix
    ltac:(cbn; discriminate) Hnil HdoneNb) as
    (? & l28 & g28 & ? & p28 & Ho27 & Hs27 & ? & Hp28).
  pose (b28 := (l28,g28)). eapply writeSuccessDefineConstCovered in Hs27;
    [|reflexivity|reflexivity]. destruct Hs27 as (-> & -> & -> & ->).
  destruct (writeSuccess15694TakeStep _ _ _ Hp28
    ltac:(unfold b28; cbn; discriminate) Hnil HdoneNb) as
    (? & l29 & g29 & ? & p29 & Ho28 & Hs28 & ? & Hp29).
  pose (b29 := (l29,g29)). eapply writeSuccessWriteRegCovered in Hs28.
  2: reflexivity. 2: exact Hx13. 2: reflexivity. 2: reflexivity.
  destruct Hs28 as (-> & -> & -> & ->).
  destruct (writeSuccess15694TakeStep _ _ _ Hp29
    ltac:(unfold b29; cbn; discriminate) Hnil HdoneNb) as
    (? & l30 & g30 & ? & p30 & Ho29 & Hs29 & ? & Hp30).
  eapply writeSuccessWriteRegCovered in Hs29.
  2: reflexivity. 2: rewrite lookup_insert_ne; last congruence; exact Hpc.
  2: reflexivity. 2: reflexivity.
  destruct Hs29 as (-> & -> & -> & ->).
  inversion Hp30; subst; last contradiction.
  eapply writeSuccessDoneTabledCovered in Hdone.
  2: reflexivity.
  2: { unfold writeSuccess101e4Regs. rewrite lookup_insert. reflexivity. }
  2: { rewrite writeSuccess101e4NextPcExact. exact Hnext. }
  destruct Hdone as (Hlabels & HafterLocal & HafterGlobal & Hspawned).
  subst labels spawned. destruct after as [afterLocal afterGlobal].
  cbn in HafterLocal, HafterGlobal |- *. subst afterLocal afterGlobal.
  split; first reflexivity.
  unfold writeSuccess101e4SuffixFinishObservations. cbn. reflexivity.
Qed.

Print Assumptions segment_101e4_suffix_finish_covered.
