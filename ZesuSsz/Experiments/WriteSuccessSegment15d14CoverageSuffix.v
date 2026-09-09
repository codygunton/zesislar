From Coq Require Import Lists.List ZArith.ZArith.
Require Import isla.riscv64.riscv64.
Require Import IslaTraces.write_success_07.a15d18.
Require Import ZesuSsz.Contracts.InstructionBoundary.
Require Import ZesuSsz.Experiments.WriteSuccessCoverageAutomation.
Require Import ZesuSsz.Experiments.WriteSuccessSegment15694.
Require Import ZesuSsz.Experiments.WriteSuccessSegment15d14.

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
  have HdoneNb := seqStepSourceBlocking _ _ _ _ _ _ Hdone.
  destruct (writeSuccess15694TakeStep _ _ _ Hprefix
    ltac:(cbn; discriminate) Hnil HdoneNb) as
    (? & l26 & g26 & ? & p26 & Ho25 & Hs25 & ? & Hp26).
  pose (b26 := (l26,g26)).
  eapply writeSuccessDefineConstCovered in Hs25;
    [|reflexivity|reflexivity]. destruct Hs25 as (-> & -> & -> & ->).
  destruct (writeSuccess15694TakeStep _ _ _ Hp26
    ltac:(unfold b26; cbn; discriminate) Hnil HdoneNb) as
    (? & l27 & g27 & ? & p27 & Ho26 & Hs26 & ? & Hp27).
  pose (b27 := (l27,g27)).
  eapply writeSuccessDefineConstCovered in Hs26;
    [|reflexivity|reflexivity]. destruct Hs26 as (-> & -> & -> & ->).
  destruct (writeSuccess15694TakeStep _ _ _ Hp27
    ltac:(unfold b27; cbn; discriminate) Hnil HdoneNb) as
    (? & l28 & g28 & ? & p28 & Ho27 & Hs27 & ? & Hp28).
  pose (b28 := (l28,g28)).
  eapply writeSuccessDeclareConstBoolCovered in Hs27; [|reflexivity].
  destruct Hs27 as (declared & -> & -> & -> & ->).
  destruct (writeSuccess15694TakeStep _ _ _ Hp28
    ltac:(unfold b28; cbn; discriminate) Hnil HdoneNb) as
    (? & l30 & g30 & ? & p30 & Ho29 & Hs29 & ? & Hp30).
  pose (b30 := (l30,g30)).
  eapply writeSuccessWriteMemBackedCovered with
    (result := RVal_Bool declared) (kind := RegVal_Poison)
    (address := writeSuccess15d14Address address) (len := 8%N) (tag := None)
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
  exists declared. split; first reflexivity.
  unfold writeSuccess15d14SuffixObservations,
    writeSuccess15d14Global, writeSuccess15d14Memory,
    writeSuccess15d14Bytes. cbn.
  reflexivity.
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
  have HdoneNb := seqStepSourceBlocking _ _ _ _ _ _ Hdone.
  destruct (writeSuccess15694TakeStep _ _ _ Hprefix
    ltac:(cbn; discriminate) Hnil HdoneNb) as
    (? & l26 & g26 & ? & p26 & Ho25 & Hs25 & ? & Hp26).
  pose (b26 := (l26,g26)).
  eapply writeSuccessDefineConstCovered in Hs25;
    [|reflexivity|reflexivity]. destruct Hs25 as (-> & -> & -> & ->).
  destruct (writeSuccess15694TakeStep _ _ _ Hp26
    ltac:(unfold b26; cbn; discriminate) Hnil HdoneNb) as
    (? & l27 & g27 & ? & p27 & Ho26 & Hs26 & ? & Hp27).
  pose (b27 := (l27,g27)).
  eapply writeSuccessDefineConstCovered in Hs26;
    [|reflexivity|reflexivity]. destruct Hs26 as (-> & -> & -> & ->).
  destruct (writeSuccess15694TakeStep _ _ _ Hp27
    ltac:(unfold b27; cbn; discriminate) Hnil HdoneNb) as
    (? & l28 & g28 & ? & p28 & Ho27 & Hs27 & ? & Hp28).
  pose (b28 := (l28,g28)).
  eapply writeSuccessDeclareConstBoolCovered in Hs27; [|reflexivity].
  destruct Hs27 as (declared & -> & -> & -> & ->).
  destruct (writeSuccess15694TakeStep _ _ _ Hp28
    ltac:(unfold b28; cbn; discriminate) Hnil HdoneNb) as
    (? & l30 & g30 & ? & p30 & Ho29 & Hs29 & ? & Hp30).
  pose (b30 := (l30,g30)).
  eapply writeSuccessWriteMemMmioCovered with
    (result := RVal_Bool declared) (kind := RegVal_Poison)
    (address := writeSuccess15d14Address address) (len := 8%N) (tag := None)
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
  exists declared. split; first reflexivity.
  unfold writeSuccess15d14MmioSuffixObservations,
    writeSuccess15d14Global. cbn.
  reflexivity.
Qed.

Print Assumptions segment_15d14_suffix_covered.
Print Assumptions segment_15d14_mmio_suffix_covered.
