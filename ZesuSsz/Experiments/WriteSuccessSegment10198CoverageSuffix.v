From Coq Require Import Lists.List ZArith.ZArith.
Require Import isla.riscv64.riscv64.
Require Import IslaTraces.write_success_01.a1019c.
Require Import ZesuSsz.Contracts.InstructionBoundary.
Require Import ZesuSsz.Experiments.WriteSuccessCoverageAutomation.
Require Import ZesuSsz.Experiments.WriteSuccessStoreCoverage.
Require Import ZesuSsz.Experiments.WriteSuccessSegment15694.
Require Import ZesuSsz.Experiments.WriteSuccessSegment10198.
Require Import ZesuSsz.Experiments.WriteSuccessStoreOutcome.

Definition writeSuccess10198SuffixObservations regs global
    (mstatusBits base satp value : bv 64) (result : bool)
    (outcome : WriteSuccessStoreOutcome) :=
  [writeSuccess10198Observation
     (writeSuccessStoreOutcomeLabels (writeSuccess10198Address base) value outcome)
     (writeSuccess15694Local
       (writeSuccess10198Trace30 mstatusBits base satp value result) regs)
     (writeSuccess10198Global global base value outcome);
   writeSuccess10198Observation []
     (writeSuccess15694Local
       (writeSuccess10198Trace31 mstatusBits base satp value result)
       (writeSuccess10198Regs regs))
     (writeSuccess10198Global global base value outcome);
   writeSuccess10198Observation []
     (writeSuccess10198After regs global base value outcome).1
     (writeSuccess10198Global global base value outcome)].

Lemma segment_10198_suffix_covered regs global
    (mstatusBits base satp value : bv 64) (result : bool)
    prefix29 done labels spawned after :
  regs !! "PC" = Some (RVal_Bits (Z_to_bv 64 0x10198)) ->
  global.(seq_instrs) !! Z_to_bv 64 0x1019c = Some a1019c ->
  IslaInstructionPrefixPath
    (writeSuccess15694Local
      (writeSuccess10198Trace29 mstatusBits base satp value result) regs,
     global) prefix29 done ->
  done.1.(seq_trace) = tnil ->
  seq_step done.1 done.2 labels after.1 after.2 spawned ->
  exists outcome,
    writeSuccessStoreOutcomePermitted global
      (writeSuccess10198Address base) outcome /\
    after = writeSuccess10198After regs global base value outcome /\
    prefix29 ++ ({| microLabels := labels; microAfter := after |} :: []) =
      writeSuccess10198SuffixObservations regs global
        mstatusBits base satp value result outcome.
Proof.
  intros Hpc Hnext Hprefix Hnil Hdone.
  have HdoneNb := seqStepSourceBlocking _ _ _ _ _ _ Hdone.
  destruct (writeSuccess15694TakeStep _ _ _ Hprefix
    ltac:(cbn; discriminate) Hnil HdoneNb) as
    (? & l30 & g30 & ? & p30 & Ho29 & Hs29 & ? & Hp30).
  pose (b30 := (l30,g30)).
  destruct (read_mem global.(seq_mem)
    (bv_unsigned (writeSuccess10198Address base)) 8) as [old|] eqn:Hmem.
  - eapply writeSuccessWriteMemBackedCovered with
      (result := RVal_Bool result) (kind := RegVal_Poison)
      (address := writeSuccess10198Address base) (len := 8%N)
      (tag := None) (value := value) in Hs29.
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
    2: { unfold writeSuccess10198Regs. rewrite lookup_insert. reflexivity. }
    2: { rewrite writeSuccess10198NextPcExact. exact Hnext. }
    destruct Hdone as (Hlabels & HafterLocal & HafterGlobal & Hspawned).
    subst labels spawned. destruct after as [afterLocal afterGlobal].
    cbn in HafterLocal, HafterGlobal |- *. subst afterLocal afterGlobal.
    exists WriteSuccessStoreBacked. split.
    + cbn. eauto.
    + split; first reflexivity.
      unfold writeSuccess10198SuffixObservations, writeSuccess10198Global,
        writeSuccess10198Memory, writeSuccessStoreOutcomeGlobal,
        writeSuccessStoreOutcomeMemory, writeSuccessStoreBytes. cbn.
      reflexivity.
  - eapply writeSuccessWriteMemMmioOutcomeCovered with
      (result := RVal_Bool result) (kind := RegVal_Poison)
      (address := writeSuccess10198Address base) (len := 8%N)
      (tag := None) (value := value) in Hs29.
    2: { unfold b30. cbn. reflexivity. }
    2: lia. 2: exact Hmem.
    destruct Hs29 as (Hrange & Houtside & -> & -> & -> & ->).
    destruct (writeSuccess15694TakeStep _ _ _ Hp30
      ltac:(unfold b30; cbn; discriminate) Hnil HdoneNb) as
      (? & l31 & g31 & ? & p31 & Ho30 & Hs30 & ? & Hp31).
    eapply writeSuccessWriteRegCovered in Hs30.
    2: reflexivity. 2: exact Hpc. 2: reflexivity. 2: reflexivity.
    destruct Hs30 as (-> & -> & -> & ->).
    inversion Hp31; subst; last contradiction.
    eapply writeSuccessDoneTabledCovered in Hdone.
    2: reflexivity.
    2: { unfold writeSuccess10198Regs. rewrite lookup_insert. reflexivity. }
    2: { rewrite writeSuccess10198NextPcExact. exact Hnext. }
    destruct Hdone as (Hlabels & HafterLocal & HafterGlobal & Hspawned).
    subst labels spawned. destruct after as [afterLocal afterGlobal].
    cbn in HafterLocal, HafterGlobal |- *. subst afterLocal afterGlobal.
    exists WriteSuccessStoreMmio. split.
    + cbn. repeat split; assumption.
    + split; first reflexivity.
      unfold writeSuccess10198SuffixObservations, writeSuccess10198Global,
        writeSuccess10198Memory, writeSuccessStoreOutcomeGlobal,
        writeSuccessStoreOutcomeMemory, writeSuccessStoreOutcomeLabels. cbn.
      reflexivity.
Qed.

Print Assumptions segment_10198_suffix_covered.
