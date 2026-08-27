Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Experiments.OperationalBridge.
Require Import ZesuSsz.Experiments.AllocatorGetOperational.
Require Import ZesuSsz.Contracts.Machine.
Require Import ZesuSsz.Generated.Level1.
Require Import ZesuSsz.Contracts.Level1.

Definition allocatorMem1 (sp : bv 64) (mem : mem_map) : mem_map :=
  write_mem 8 mem (sp + Z_to_bv 64 16)%bv 0x2401a0b0.

Definition allocatorMem2 (sp : bv 64) (mem : mem_map) : mem_map :=
  write_mem 8 (allocatorMem1 sp mem)
    (sp + Z_to_bv 64 24)%bv 0x177a8.

Definition allocatorCanonicalEntry (args : AllocatorGetArgs)
    (state : OperationalState) : Prop :=
  exists (sp x10 x11 x12 x13 stack0 stack8 : bv 64) regs
      mem old16 old24,
    bv_unsigned sp = allocatorStackPointer args /\
    bv_unsigned sp `mod` 8 = 0 /\
    0x20000000 <= bv_unsigned sp /\
    bv_unsigned sp + 24 < 0x40000000 /\
    read_mem mem (bv_unsigned sp) 8 = Some (bv_to_bvn stack0) /\
    read_mem mem (bv_unsigned sp + 8) 8 = Some (bv_to_bvn stack8) /\
    read_mem mem (bv_unsigned sp + 16) 8 = Some old16 /\
    read_mem (allocatorMem1 sp mem) (bv_unsigned sp + 24) 8 = Some old24 /\
    allocatorSystemContext regs /\
    regs !! "PC" = Some (RVal_Bits (Z_to_bv 64 0x14ccc)) /\
    regs !! "x2" = Some (RVal_Bits sp) /\
    regs !! "x10" = Some (RVal_Bits x10) /\
    regs !! "x11" = Some (RVal_Bits x11) /\
    regs !! "x12" = Some (RVal_Bits x12) /\
    regs !! "x13" = Some (RVal_Bits x13) /\
    state = allocatorState regs mem.

Definition allocatorCanonicalPost (args : AllocatorGetArgs)
    (outcome : AllocatorGetOutcome) (before after : OperationalState) : Prop :=
  exists (sp x10 x11 x12 x13 stack0 stack8 : bv 64) regs mem,
    bv_unsigned sp = allocatorStackPointer args /\
    outcome = Build_AllocatorGetOutcome 0x2401a0b0 0x177a8 /\
    before = allocatorState regs mem /\
    after = allocatorState
      (allocatorR8
        (allocatorR7
          (allocatorR6
            (allocatorR5
              (allocatorR4 stack0
                (allocatorR3 stack8
                  (allocatorR2
                    (allocatorR1
                      regs))))))))
      (allocatorMem2 sp mem).

Definition allocatorCanonicalModel :
    Level1MachineModel OperationalState unit := {|
  endpointStep := operationalInstructionStep;
  endpointPc := operationalPc;
  readInputEntry := fun _ _ => False;
  readInputExit := fun _ _ _ _ => False;
  allocatorGetEntry := allocatorCanonicalEntry;
  allocatorGetExit := allocatorCanonicalPost;
  decodeBoundaryEntry := fun _ _ => False;
  decodeBoundaryExit := fun _ _ _ _ => False;
  writeSuccessEntry := fun _ _ => False;
  writeSuccessExit := fun _ _ _ _ => False;
  writeFailureEntry := fun _ _ => False;
  writeFailureExit := fun _ _ _ _ => False;
  zkvmExitEntry := fun _ _ => False;
  zkvmExitPost := fun _ _ _ _ => False;
  referenceDecodes := fun _ _ => False;
  decodedResultRelModuloKnownBugs := fun _ _ _ => False;
  avoidsReviewedDomainDivergences := fun _ _ => False;
  knownBugApplies := fun _ _ _ => False;
  decodeObservationSuccess := fun _ _ => False;
  decodeObservationFailure := fun _ => False
|}.

Ltac allocator_region :=
  unfold PcInRanges;
  eexists 0x14ccc, 0x14cec; split;
  [ cbn; left; reflexivity | lia ].

Lemma allocatorCanonicalImplements :
  Implements allocatorCanonicalModel
    (PcInRanges allocatorGetExecutionPcRanges)
    (PcInList allocatorGetExitPcs)
    (allocatorGetContract allocatorCanonicalModel (fun _ => 8%nat)).
Proof.
  unfold Implements, ContractImplements.
  intros args fromStep before
    (sp & x10 & x11 & x12 & x13 & stack0 & stack8 & regs & mem &
      old16 & old24 & HspValue & Halign & Hlow & Hhigh & Hread0 &
      Hread8 & Hread16 & Hread24 & Hsys0 & Hpc0 & Hx20 & Hx100 &
      Hx110 & Hx120 & Hx130 & ->).
  set r1 := allocatorR1 regs.
  set r2 := allocatorR2 r1.
  set r3 := allocatorR3 stack8 r2.
  set r4 := allocatorR4 stack0 r3.
  set r5 := allocatorR5 r4.
  set r6 := allocatorR6 r5.
  set r7 := allocatorR7 r6.
  set r8 := allocatorR8 r7.
  set mem1 := allocatorMem1 sp mem.
  set mem2 := allocatorMem2 sp mem.
  assert (Hsys1 : allocatorSystemContext r1).
  { unfold r1. apply allocatorSystemContextR1. exact Hsys0. }
  assert (Hsys2 : allocatorSystemContext r2).
  { unfold r2. apply allocatorSystemContextR2. exact Hsys1. }
  assert (Hsys3 : allocatorSystemContext r3).
  { unfold r3. apply allocatorSystemContextR3. exact Hsys2. }
  assert (Hsys4 : allocatorSystemContext r4).
  { unfold r4. apply allocatorSystemContextR4. exact Hsys3. }
  assert (Hsys5 : allocatorSystemContext r5).
  { unfold r5. apply allocatorSystemContextR5. exact Hsys4. }
  assert (Hsys6 : allocatorSystemContext r6).
  { unfold r6. apply allocatorSystemContextR6. exact Hsys5. }
  assert (Hsys7 : allocatorSystemContext r7).
  { unfold r7. apply allocatorSystemContextR7. exact Hsys6. }
  assert (Hpc1 : r1 !! "PC" =
      Some (RVal_Bits (Z_to_bv 64 0x14cd0))).
  { unfold r1. apply allocatorPcR1. }
  assert (Hpc2 : r2 !! "PC" =
      Some (RVal_Bits (Z_to_bv 64 0x14cd4))).
  { unfold r2. apply allocatorPcR2. }
  assert (Hpc3 : r3 !! "PC" =
      Some (RVal_Bits (Z_to_bv 64 0x14cd8))).
  { unfold r3. apply allocatorPcR3. }
  assert (Hpc4 : r4 !! "PC" =
      Some (RVal_Bits (Z_to_bv 64 0x14cdc))).
  { unfold r4. apply allocatorPcR4. }
  assert (Hpc5 : r5 !! "PC" =
      Some (RVal_Bits (Z_to_bv 64 0x14ce0))).
  { unfold r5. apply allocatorPcR5. }
  assert (Hpc6 : r6 !! "PC" =
      Some (RVal_Bits (Z_to_bv 64 0x14ce4))).
  { unfold r6. apply allocatorPcR6. }
  assert (Hpc7 : r7 !! "PC" =
      Some (RVal_Bits (Z_to_bv 64 0x14ce8))).
  { unfold r7. apply allocatorPcR7. }
  assert (Hpc8 : r8 !! "PC" =
      Some (RVal_Bits (Z_to_bv 64 0x14cec))).
  { unfold r8. apply allocatorPcR8. }
  assert (Hx111 : r1 !! "x11" = Some (RVal_Bits x11)).
  { unfold r1. apply allocatorR1X11. exact Hx110. }
  assert (Hx22 : r2 !! "x2" = Some (RVal_Bits sp)).
  { unfold r2, r1. apply allocatorR2X2. exact Hx20. }
  assert (Hx132 : r2 !! "x13" = Some (RVal_Bits x13)).
  { unfold r2, r1. apply allocatorR2X13. exact Hx130. }
  assert (Hx23 : r3 !! "x2" = Some (RVal_Bits sp)).
  { unfold r3, r2, r1. apply allocatorR3X2. exact Hx20. }
  assert (Hx123 : r3 !! "x12" = Some (RVal_Bits x12)).
  { unfold r3, r2, r1. apply allocatorR3X12. exact Hx120. }
  assert (Hx104 : r4 !! "x10" =
      Some (RVal_Bits (Z_to_bv 64 0x24019ccc))).
  { unfold r4, r3, r2, r1. apply allocatorR4X10. }
  assert (Hx115 : r5 !! "x11" =
      Some (RVal_Bits (Z_to_bv 64 0x17cd0))).
  { unfold r5, r4, r3, r2, r1. apply allocatorR5X11. }
  assert (Hx26 : r6 !! "x2" = Some (RVal_Bits sp)).
  { unfold r6, r5, r4, r3, r2, r1.
    apply allocatorR6X2. exact Hx20. }
  assert (Hx106 : r6 !! "x10" =
      Some (RVal_Bits (Z_to_bv 64 0x2401a0b0))).
  { unfold r6, r5, r4, r3, r2, r1. apply allocatorR6X10. }
  assert (Hx27 : r7 !! "x2" = Some (RVal_Bits sp)).
  { unfold r7, r6, r5, r4, r3, r2, r1.
    apply allocatorR7X2. exact Hx20. }
  assert (Hx117 : r7 !! "x11" =
      Some (RVal_Bits (Z_to_bv 64 0x177a8))).
  { unfold r7, r6, r5, r4, r3, r2, r1. apply allocatorR7X11. }
  eexists 8%nat, (allocatorState r8 mem2),
    {| allocatorStateAddress := 0x2401a0b0;
       allocatorVtableAddress := 0x177a8 |}.
  repeat split.
  - lia.
  - reflexivity.
  - eapply ConfinedTraceStep with
      (address := 0x14ccc) (middle := allocatorState r1 mem).
    + cbn. rewrite Hpc0. reflexivity.
    + allocator_region.
    + eapply allocatorAuipc10StepAny; eauto.
    + eapply ConfinedTraceStep with
        (address := 0x14cd0) (middle := allocatorState r2 mem).
      * cbn. rewrite Hpc1. reflexivity.
      * allocator_region.
      * eapply allocatorAuipc11StepAny.
        -- exact Hsys1.
        -- exact Hpc1.
        -- exact Hx111.
      * eapply ConfinedTraceStep with
          (address := 0x14cd4) (middle := allocatorState r3 mem).
        -- cbn. rewrite Hpc2. reflexivity.
        -- allocator_region.
        -- eapply allocatorLoad13StepAny with
             (sp := sp) (oldX13 := x13) (stack8 := stack8).
           ++ exact Hsys2.
           ++ exact Hpc2.
           ++ exact Hx22.
           ++ exact Hx132.
           ++ exact Halign.
           ++ exact Hlow.
           ++ exact Hhigh.
           ++ exact Hread8.
        -- eapply ConfinedTraceStep with
            (address := 0x14cd8) (middle := allocatorState r4 mem).
           ++ cbn. rewrite Hpc3. reflexivity.
           ++ allocator_region.
           ++ eapply allocatorLoad12StepAny with
                (sp := sp) (oldX12 := x12) (stack0 := stack0).
              ** exact Hsys3.
              ** exact Hpc3.
              ** exact Hx23.
              ** exact Hx123.
              ** exact Halign.
              ** exact Hlow.
              ** exact Hhigh.
              ** exact Hread0.
           ++ eapply ConfinedTraceStep with
               (address := 0x14cdc) (middle := allocatorState r5 mem).
              ** cbn. rewrite Hpc4. reflexivity.
              ** allocator_region.
              ** apply allocatorAdd10StepAny.
                 --- exact Hsys4.
                 --- exact Hpc4.
                 --- exact Hx104.
              ** eapply ConfinedTraceStep with
                  (address := 0x14ce0) (middle := allocatorState r6 mem).
                 --- cbn. rewrite Hpc5. reflexivity.
                 --- allocator_region.
                 --- apply allocatorAdd11StepAny.
                     +++ exact Hsys5.
                     +++ exact Hpc5.
                     +++ exact Hx115.
                 --- eapply ConfinedTraceStep with
                     (address := 0x14ce4)
                     (middle := allocatorState r7 mem1).
                     +++ cbn. rewrite Hpc6. reflexivity.
                     +++ allocator_region.
                     +++ eapply allocatorStore10StepAny with
                           (sp := sp) (x10 := Z_to_bv 64 0x2401a0b0)
                           (old := old16).
                         *** exact Hsys6.
                         *** exact Hpc6.
                         *** exact Hx26.
                         *** exact Hx106.
                         *** exact Halign.
                         *** exact Hlow.
                         *** exact Hhigh.
                         *** exact Hread16.
                     +++ eapply ConfinedTraceStep with
                         (address := 0x14ce8)
                         (middle := allocatorState r8 mem2).
                         *** cbn. rewrite Hpc7. reflexivity.
                         *** allocator_region.
                         *** eapply allocatorStore11StepAny with
                               (sp := sp) (x11 := Z_to_bv 64 0x177a8)
                               (old := old24).
                             ---- exact Hsys7.
                             ---- exact Hpc7.
                             ---- exact Hx27.
                             ---- exact Hx117.
                             ---- exact Halign.
                             ---- exact Hlow.
                             ---- exact Hhigh.
                             ---- subst mem1. exact Hread24.
                         *** constructor.
  - eexists 0x14cec. split.
    + cbn. rewrite Hpc8. reflexivity.
    + cbn. left. reflexivity.
  - cbn.
    eexists sp, x10, x11, x12, x13, stack0, stack8, regs, mem.
    repeat split; try assumption.
Qed.

Theorem level1AllocatorCanonical :
  exists bound, InputIndexedBound bound /\
    Implements allocatorCanonicalModel
      (PcInRanges allocatorGetExecutionPcRanges)
      (PcInList allocatorGetExitPcs)
      (allocatorGetContract allocatorCanonicalModel
        (fun args => bound (length (allocatorInput args)))).
Proof.
  eexists (fun _ => 8%nat). split.
  - intros size _. unfold level1ContractFuel.
    pose proof (Nat.pow_gt_lin_r 2 160 ltac:(lia)) as Hbound. lia.
  - exact allocatorCanonicalImplements.
Qed.
