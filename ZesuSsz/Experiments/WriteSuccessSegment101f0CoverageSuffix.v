From Coq Require Import Lists.List ZArith.ZArith.
Require Import isla.riscv64.riscv64.
Require Import IslaTraces.write_success_02.a101f4.
Require Import ZesuSsz.Contracts.InstructionBoundary.
Require Import ZesuSsz.Experiments.WriteSuccessCoverageAutomation.
Require Import ZesuSsz.Experiments.WriteSuccessSegment15694.
Require Import ZesuSsz.Experiments.WriteSuccessSegment101f0.

Definition writeSuccess101f0SuffixObservations regs global
    (mstatusBits address satp value : bv 64) (result : bool) :=
  [writeSuccess15694Observation
     (writeSuccess15694Local
       (writeSuccess101f0Trace30 mstatusBits address satp value result) regs)
     (writeSuccess101f0Global global address value);
   writeSuccess15694Observation
     (writeSuccess15694Local
       (writeSuccess101f0Trace31 mstatusBits address satp value result)
       (writeSuccess101f0Regs regs))
     (writeSuccess101f0Global global address value);
   writeSuccess15694Observation
     (writeSuccess101f0After regs global address value).1
     (writeSuccess101f0Global global address value)].

Lemma segment_101f0_suffix_covered regs global
    (mstatusBits address satp value : bv 64) (result : bool) old
    prefix29 done labels spawned after :
  regs !! "PC" = Some (RVal_Bits (Z_to_bv 64 0x101f0)) ->
  read_mem global.(seq_mem) (bv_unsigned address) 1 = Some old ->
  global.(seq_instrs) !! Z_to_bv 64 0x101f4 = Some a101f4 ->
  IslaInstructionPrefixPath
    (writeSuccess15694Local
      (writeSuccess101f0Trace29 mstatusBits address satp value result) regs,
     global)
    prefix29 done ->
  done.1.(seq_trace) = tnil ->
  seq_step done.1 done.2 labels after.1 after.2 spawned ->
  after = writeSuccess101f0After regs global address value /\
  prefix29 ++ ({| microLabels := labels; microAfter := after |} :: []) =
    writeSuccess101f0SuffixObservations regs global
      mstatusBits address satp value result.
Proof.
  intros Hpc Hmem Hnext Hprefix Hnil Hdone.
  have HdoneNb := seqStepSourceBlocking _ _ _ _ _ _ Hdone.
  destruct (writeSuccess15694TakeStep _ _ _ Hprefix
    ltac:(cbn; discriminate) Hnil HdoneNb) as
    (? & l30 & g30 & ? & p30 & Ho29 & Hs29 & ? & Hp30).
  pose (b30 := (l30,g30)).
  eapply writeSuccessWriteMemBackedCovered with
    (result := RVal_Bool result) (kind := RegVal_Poison)
    (address := address) (len := 1%N) (tag := None)
    (value := writeSuccess101f0Byte value) in Hs29.
  2: { unfold b30, writeSuccess101f0Byte. cbn. reflexivity. }
  2: lia. 2: exact Hmem.
  destruct Hs29 as (-> & -> & -> & ->).
  destruct (writeSuccess15694TakeStep _ _ _ Hp30
    ltac:(unfold b30; cbn; discriminate) Hnil HdoneNb) as
    (? & l31 & g31 & ? & p31 & Ho30 & Hs30 & ? & Hp31).
  eapply writeSuccessWriteRegCovered in Hs30.
  2: reflexivity. 2: exact Hpc. 2: reflexivity. 2: reflexivity.
  destruct Hs30 as (-> & -> & -> & ->).
  inversion Hp31; subst; last contradiction.
  eapply writeSuccessDoneTabledCovered in Hdone.
  2: reflexivity.
  2: { unfold writeSuccess101f0Regs. rewrite lookup_insert. reflexivity. }
  2: { rewrite writeSuccess101f0NextPcExact. exact Hnext. }
  destruct Hdone as (Hlabels & HafterLocal & HafterGlobal & Hspawned).
  subst labels spawned. destruct after as [afterLocal afterGlobal].
  cbn in HafterLocal, HafterGlobal |- *. subst afterLocal afterGlobal.
  split; first reflexivity.
  unfold writeSuccess101f0SuffixObservations,
    writeSuccess101f0Global, writeSuccess101f0Memory,
    writeSuccess101f0Bytes. cbn.
  reflexivity.
Qed.

Print Assumptions segment_101f0_suffix_covered.
