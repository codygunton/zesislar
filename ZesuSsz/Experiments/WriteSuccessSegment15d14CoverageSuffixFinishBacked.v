From Coq Require Import Lists.List ZArith.ZArith.
Require Import isla.riscv64.riscv64.
Require Import IslaTraces.write_success_07.a15d18.
Require Import ZesuSsz.Contracts.InstructionBoundary.
Require Import ZesuSsz.Experiments.WriteSuccessCoverageAutomation.
Require Import ZesuSsz.Experiments.WriteSuccessSegment15694.
Require Import ZesuSsz.Experiments.WriteSuccessSegment15d14.

Definition writeSuccess15d14SuffixFinishBackedObservations regs global
    (mstatusBits base satp value : bv 64) (result : bool) :=
  [ {| microLabels := [];
      microAfter := (writeSuccess15694Local
        (writeSuccess15d14Trace30 mstatusBits base satp value result) regs, writeSuccess15d14Global global base value) |};
   writeSuccess15694Observation
     (writeSuccess15694Local
       (writeSuccess15d14Trace31 mstatusBits base satp value result)
       (writeSuccess15d14Regs regs)) (writeSuccess15d14Global global base value);
   writeSuccess15694Observation (writeSuccess15d14After regs global base value).1 (writeSuccess15d14Global global base value)].

Lemma segment_15d14_suffix_finish_backed_covered regs global
    (mstatusBits base satp value : bv 64) (result : bool) old prefix29 done labels spawned after :
  regs !! "PC" = Some (RVal_Bits (Z_to_bv 64 0x15d14)) ->
  read_mem global.(seq_mem) (bv_unsigned (writeSuccess15d14Address base)) 8 = Some old ->
  global.(seq_instrs) !! Z_to_bv 64 0x15d18 = Some a15d18 ->
  IslaInstructionPrefixPath
    (writeSuccess15694Local
      (writeSuccess15d14Trace29 mstatusBits base satp value result) regs, global)
    prefix29 done ->
  done.1.(seq_trace) = tnil ->
  seq_step done.1 done.2 labels after.1 after.2 spawned ->
  after = writeSuccess15d14After regs global base value /\
  prefix29 ++ ({| microLabels := labels; microAfter := after |} :: []) =
    writeSuccess15d14SuffixFinishBackedObservations regs global mstatusBits base satp value result.
Proof.
  intros Hpc Hmem Hnext Hprefix Hnil Hdone.
  have HdoneNb := seqStepSourceBlocking _ _ _ _ _ _ Hdone.
  destruct (writeSuccess15694TakeStep _ _ _ Hprefix
    ltac:(cbn; discriminate) Hnil HdoneNb) as
    (? & l30 & g30 & ? & p30 & Ho29 & Hs29 & ? & Hp30).
  pose (b30 := (l30,g30)).
  eapply writeSuccessWriteMemBackedCovered with
    (result := RVal_Bool result) (kind := RegVal_Poison)
    (address := writeSuccess15d14Address base) (len := 8%N) (tag := None)
    (value := value) in Hs29.
  2: { unfold b30. cbn. reflexivity. }
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
  2: { unfold writeSuccess15d14Regs. rewrite lookup_insert. reflexivity. }
  2: { rewrite writeSuccess15d14NextPcExact. exact Hnext. }
  destruct Hdone as (Hlabels & HafterLocal & HafterGlobal & Hspawned).
  subst labels spawned. destruct after as [afterLocal afterGlobal].
  cbn in HafterLocal, HafterGlobal |- *. subst afterLocal afterGlobal.
  split; first reflexivity.
  unfold writeSuccess15d14SuffixFinishBackedObservations,
    writeSuccess15d14Global, writeSuccess15d14Memory,
    writeSuccess15d14Bytes. cbn.
  reflexivity.
Qed.

Print Assumptions segment_15d14_suffix_finish_backed_covered.
