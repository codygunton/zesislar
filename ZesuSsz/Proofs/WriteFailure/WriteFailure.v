Require Import ZesuSsz.Automation.All.
Require Import ZesuMachineMap.Machine.
Require Import ZesuSsz.Automation.Hooks.
Require Import isla.riscv64.riscv64.
From IslaTraces.write_failure Require Import instrs.
Require Import ZesuSsz.Contracts.IslarisMachine.
Require Import ZesuSsz.Generated.Level1.
Require Import ZesuSsz.Contracts.Endpoints.
Require Import ZesuSsz.Export.Snapshots.
Require Import ZesuSsz.Export.Adequacy.

Import ZesuSsz.Automation.Hooks.

Definition failureObservation : ByteString :=
  [0x5a; 0x53; 0x53; 0x5a; 0x01; 0x00].

Definition failureMemory : list (bv 8) :=
  [BV 8 0x5a; BV 8 0x53; BV 8 0x53; BV 8 0x5a; BV 8 0x01; BV 8 0x00].

Definition write_failure_resources `{!islaG Sigma} `{!threadG} :
    IslarisContractResources WriteFailureArgs ByteString := {|
  islarisCode :=
    (instr 0x161c0 (Some a161c0) ∗ instr 0x161c4 (Some a161c4) ∗
     instr 0x161c8 (Some a161c8) ∗ instr 0x161cc (Some a161cc) ∗
     instr 0x161d0 (Some a161d0) ∗ instr 0x10190 (Some a10190) ∗
     instr 0x10194 (Some a10194) ∗ instr 0x10198 (Some a10198) ∗
     instr 0x1019c (Some a1019c) ∗ instr 0x101a0 (Some a101a0))%I;
  islarisEntry := fun args =>
    (∃ (old_x5 old_x6 old_x10 old_x11 old_pointer old_length : bv 64),
      ⌜failureReturnAddress args = 0x14d24⌝ ∗
      reg_col zesu_sys_regs ∗
      "x1" ↦ᵣ RVal_Bits (BV 64 0x14d24) ∗
      "x5" ↦ᵣ RVal_Bits old_x5 ∗ "x6" ↦ᵣ RVal_Bits old_x6 ∗
      "x10" ↦ᵣ RVal_Bits old_x10 ∗ "x11" ↦ᵣ RVal_Bits old_x11 ∗
      0x177c8 ↦ₘ∗ failureMemory ∗
      (machineOutputAddress defaultMap) ↦ₘ old_pointer ∗ (machineOutputSizeAddress defaultMap) ↦ₘ old_length ∗ True)%I;
  islarisExit := fun args bytes =>
    (⌜failureReturnAddress args = 0x14d24⌝ ∗
     ⌜bytes = failureObservation⌝ ∗
     reg_col zesu_sys_regs ∗
     "x1" ↦ᵣ RVal_Bits (BV 64 0x14d24) ∗
     "x5" ↦ᵣ RVal_Bits (BV 64 (mapIoContextAddress defaultMap)) ∗
     "x6" ↦ᵣ RVal_Bits (BV 64 0x101cc) ∗
     "x10" ↦ᵣ RVal_Bits (BV 64 0x177c8) ∗
     "x11" ↦ᵣ RVal_Bits (BV 64 6) ∗
     0x177c8 ↦ₘ∗ failureMemory ∗
     (machineOutputAddress defaultMap) ↦ₘ (BV 64 0x177c8) ∗
     (machineOutputSizeAddress defaultMap) ↦ₘ (BV 64 6) ∗ True)%I
|}.

Definition writeFailureAllows
    (_ : WriteFailureArgs) (bytes : ByteString) : Prop :=
  bytes = failureObservation.

Theorem write_failure_state_correct `{!islaG Sigma} `{!threadG} :
  ⊢ IslarisContractSpec 0x161c0 0x14d24
    writeFailureAllows write_failure_resources.
Proof.
  rewrite /IslarisContractSpec /write_failure_resources /writeFailureAllows /=.
  zesu_block.
Qed.

Definition writeFailureOutputTraceSpec `{!islaG Sigma} `{!threadG}
    (data size ret : bv 64) (payload : list (bv 8))
    (tail : spec) (P : iProp Sigma) : iProp Sigma :=
  (∃ (old_x5 : bv 64),
    reg_col zesu_sys_regs ∗
    "x1" ↦ᵣ RVal_Bits ret ∗ "x5" ↦ᵣ RVal_Bits old_x5 ∗
    "x10" ↦ᵣ RVal_Bits data ∗ "x11" ↦ᵣ RVal_Bits size ∗
    bv_unsigned data ↦ₘ∗ payload ∗ mmio_range (machineOutputAddress defaultMap) 16 ∗
    spec_trace (writeOutputEvents data size payload tail) ∗
    ⌜Z.to_N (bv_unsigned size) = N.of_nat (length payload)⌝ ∗
    ⌜bv_extract 0 1 ret = BV 1 0⌝ ∗
    ⌜bv_extract 1 1 ret = BV 1 0⌝ ∗
    ⌜bv_extract 0 2 ret = BV 2 0⌝ ∗ P ∗
    instr_pre (bv_unsigned ret)
      (reg_col zesu_sys_regs ∗
       "x1" ↦ᵣ RVal_Bits ret ∗
       "x5" ↦ᵣ RVal_Bits (BV 64 (mapIoContextAddress defaultMap)) ∗
       "x10" ↦ᵣ RVal_Bits data ∗ "x11" ↦ᵣ RVal_Bits size ∗
       bv_unsigned data ↦ₘ∗ payload ∗ mmio_range (machineOutputAddress defaultMap) 16 ∗ spec_trace tail ∗ P ∗ True) ∗ True)%I.

Global Instance : LithiumUnfold (@writeFailureOutputTraceSpec) := I.

Definition writeFailureTraceTail : spec :=
  scons (SInstrTrap (BV 64 0x14d24)) snil.

Definition writeFailureTraceEntry `{!islaG Sigma} `{!threadG} : iProp Sigma :=
  (∃ (old_x5 old_x6 old_x10 old_x11 : bv 64),
    reg_col zesu_sys_regs ∗
    "x1" ↦ᵣ RVal_Bits (BV 64 0x14d24) ∗
    "x5" ↦ᵣ RVal_Bits old_x5 ∗ "x6" ↦ᵣ RVal_Bits old_x6 ∗
    "x10" ↦ᵣ RVal_Bits old_x10 ∗ "x11" ↦ᵣ RVal_Bits old_x11 ∗
    0x177c8 ↦ₘ∗ failureMemory ∗ mmio_range (machineOutputAddress defaultMap) 16 ∗
    spec_trace (writeOutputEvents (BV 64 0x177c8) (BV 64 6)
      failureMemory writeFailureTraceTail) ∗
    instr_pre 0x14d24
      (reg_col zesu_sys_regs ∗
       "x1" ↦ᵣ RVal_Bits (BV 64 0x14d24) ∗
       "x5" ↦ᵣ RVal_Bits (BV 64 (mapIoContextAddress defaultMap)) ∗
       "x10" ↦ᵣ RVal_Bits (BV 64 0x177c8) ∗
       "x11" ↦ᵣ RVal_Bits (BV 64 6) ∗
       0x177c8 ↦ₘ∗ failureMemory ∗ mmio_range (machineOutputAddress defaultMap) 16 ∗ spec_trace writeFailureTraceTail ∗
       ("x6" ↦ᵣ RVal_Bits (BV 64 0x101cc) ∗ True) ∗ True) ∗
    True)%I.

Global Instance : LithiumUnfold (@writeFailureTraceEntry) := I.

Lemma write_failure_trace_prefix_correct `{!islaG Sigma} `{!threadG} :
  (instr 0x161c0 (Some a161c0) ∗ instr 0x161c4 (Some a161c4) ∗
   instr 0x161c8 (Some a161c8) ∗ instr 0x161cc (Some a161cc) ∗
   instr 0x161d0 (Some a161d0))%I -∗
  instr_body 0x10190
    (writeFailureOutputTraceSpec (BV 64 0x177c8) (BV 64 6) (BV 64 0x14d24)
      failureMemory writeFailureTraceTail
      ("x6" ↦ᵣ RVal_Bits (BV 64 0x101cc) ∗ True)) -∗
  instr_body 0x161c0 writeFailureTraceEntry.
Proof.
  move => * /=.
  iStartProof.
  liARun.
  Unshelve. all: prepare_sidecond.
  all: try assumption.
  all: try bv_solve.
  all: lazymatch goal with |- ?G => fail "side condition" G end.
Qed.

Print Assumptions write_failure_trace_prefix_correct.

Definition writeFailureInstrTable : gmap addr isla_trace :=
  <[ BV 64 0x161c0 := a161c0 ]> $
  <[ BV 64 0x161c4 := a161c4 ]> $
  <[ BV 64 0x161c8 := a161c8 ]> $
  <[ BV 64 0x161cc := a161cc ]> $
  <[ BV 64 0x161d0 := a161d0 ]> $
  <[ BV 64 0x10190 := a10190 ]> $
  <[ BV 64 0x10194 := a10194 ]> $
  <[ BV 64 0x10198 := a10198 ]> $
  <[ BV 64 0x1019c := a1019c ]> $
  <[ BV 64 0x101a0 := a101a0 ]> $ ∅.

Definition writeFailureInitialMemory : mem_map :=
  <[ BV 64 0x177c8 := BV 8 0x5a ]> $
  <[ BV 64 0x177c9 := BV 8 0x53 ]> $
  <[ BV 64 0x177ca := BV 8 0x53 ]> $
  <[ BV 64 0x177cb := BV 8 0x5a ]> $
  <[ BV 64 0x177cc := BV 8 0x01 ]> $
  <[ BV 64 0x177cd := BV 8 0x00 ]> ∅.

Definition writeFailureInitialRegs (mstatusBits satp : bv 64) : reg_map :=
  <[ "PC" := RVal_Bits (BV 64 0x161c0) ]> $
  <[ "x1" := RVal_Bits (BV 64 0x14d24) ]> $
  <[ "x5" := RVal_Bits (BV 64 0) ]> $
  <[ "x6" := RVal_Bits (BV 64 0) ]> $
  <[ "x10" := RVal_Bits (BV 64 0) ]> $
  <[ "x11" := RVal_Bits (BV 64 0) ]> $
  zesu_ram_sys_regs_map mstatusBits satp.

Lemma write_failure_output_trace_correct `{!islaG Sigma} `{!threadG}
    (data size : bv 64) (payload : list (bv 8))
    (tail : spec) (P : iProp Sigma) :
  ([∗ list] instruction ∈ skipn 5 IslaTraces.write_failure.instrs.instr_map,
    instr instruction.1 (Some instruction.2))%I -∗
  instr_body 0x10190
    (writeFailureOutputTraceSpec data size (BV 64 0x14d24)
      payload tail P).
Proof.
  move => * /=.
  iStartProof.
  unshelve (repeat zesu_liAStepNoWrite).
  Unshelve. all: try zesu_solve_pending_sidecond.
  Unshelve.
  zesu_liAStepGenericWrite.
  Unshelve.
  unshelve (repeat zesu_liAStepNoWrite).
  Unshelve. all: try zesu_solve_pending_sidecond.
  Unshelve.
  zesu_liAStepSnapshotWriteAt (bv_unsigned data).
  Unshelve.
  unshelve (repeat zesu_liAStepNoWrite).
  all: try zesu_solve_pending_sidecond.
  iExists ((fun snapshot =>
    read_mem_list snapshot.(snap_mem) (bv_unsigned data)
      (Z.to_N (bv_unsigned size)) = Some payload), tail, tt)ₗ.
  iSplit.
  { iPureIntro. intros snapshot Hmemory.
    inversion Hmemory as [|[address bytes] claims Hhead Htail]; subst.
    rewrite H0. exact Hhead. }
  iSplit; first (iPureIntro; reflexivity).
  unshelve (repeat zesu_liAStepNoWrite).
  Unshelve. all: prepare_sidecond.
  all: try assumption.
  all: try bv_solve.
  all: lazymatch goal with |- ?G => fail "side condition" G end.
Qed.

Lemma write_failure_adequate mstatusBits satp labels threads globalState steps :
  Z.land (bv_unsigned mstatusBits) 0x20000 = 0 ->
  nsteps steps
    (initial_local_state <$> [writeFailureInitialRegs mstatusBits satp],
      {| seq_instrs := writeFailureInstrTable;
         seq_mem := writeFailureInitialMemory |})
    labels (threads, globalState) ->
  (forall thread, thread ∈ threads -> not_stuck thread globalState) /\
  writeOutputEvents (BV 64 0x177c8) (BV 64 6) failureMemory
    writeFailureTraceTail labels.
Proof.
  intros Hstatus Hsteps.
  set Sigma : gFunctors := #[islaΣ].
  apply: (zesu_adequacy Sigma) => //.
  { unfold writeOutputEvents, scons. naive_solver. }
  iIntros (?) "#Hinstructions #Hbacked Hspec Hmemory /= !>".
  iSplitL => //. iIntros (?).
  rewrite /writeFailureInitialRegs /zesu_ram_sys_regs_map.
  repeat (rewrite big_sepM_insert; [|by vm_compute]).
  iIntros "(HPC&Hx1&Hx5&Hx6&Hx10&Hx11&Hpmp&Hmis&Hbase&Hsize&
    Hrombase&Hromsize&Hclbase&Hclsize&Hhtif&Hpriv&Hmisa&Hmtvec&Hmstatus&
    Hsatp&_)".
  iApply wp_asm_thread_ctx. iIntros (?) "Hcontext".
  iMod (zesu_ram_sys_regs_init with "Hcontext [Hpmp Hmis Hbase Hsize
    Hrombase Hromsize Hclbase Hclsize Hhtif Hpriv Hmisa Hmtvec Hmstatus
    Hsatp]") as "[$ Hsystem]"; first done.
  { rewrite /zesu_ram_sys_regs_map.
    repeat (rewrite big_sepM_insert; [|by vm_compute]).
    rewrite big_sepM_empty. iFrame. }
  iModIntro.
  iAssert (0x177c8 ↦ₘ∗ failureMemory)%I with "[Hmemory]" as "Hpayload".
  { rewrite /zip_with /failureMemory /=.
    iDestruct "Hmemory" as "(Hb0&Hb1&Hb2&Hb3&Hb4&Hb5&_)".
    have Haddr0 : bv_unsigned ((BV 64 0x177c8) `+Z` 0) = 0x177c8 by
      bv_solve.
    have Haddr1 : bv_unsigned ((BV 64 0x177c8) `+Z` 1) = 0x177c9 by
      bv_solve.
    have Haddr2 : bv_unsigned ((BV 64 0x177c8) `+Z` 2) = 0x177ca by
      bv_solve.
    have Haddr3 : bv_unsigned ((BV 64 0x177c8) `+Z` 3) = 0x177cb by
      bv_solve.
    have Haddr4 : bv_unsigned ((BV 64 0x177c8) `+Z` 4) = 0x177cc by
      bv_solve.
    have Haddr5 : bv_unsigned ((BV 64 0x177c8) `+Z` 5) = 0x177cd by
      bv_solve.
    iEval (rewrite Haddr0) in "Hb0".
    iEval (rewrite Haddr1) in "Hb1".
    iEval (rewrite Haddr2) in "Hb2".
    iEval (rewrite Haddr3) in "Hb3".
    iEval (rewrite Haddr4) in "Hb4".
    iEval (rewrite Haddr5) in "Hb5".
    rewrite mem_mapsto_array_eq /mem_mapsto_array_def.
    iExists 1%N. iSplit; first done.
    iSplit; first (iPureIntro; split; vm_compute).
    all: simpl; try congruence.
    iFrame. }
  iAssert (instr 0x161c0 (Some a161c0))%I as "#Hi1".
  { by unshelve iApply (instr_intro with "Hinstructions"). }
  iAssert (instr 0x161c4 (Some a161c4))%I as "#Hi2".
  { by unshelve iApply (instr_intro with "Hinstructions"). }
  iAssert (instr 0x161c8 (Some a161c8))%I as "#Hi3".
  { by unshelve iApply (instr_intro with "Hinstructions"). }
  iAssert (instr 0x161cc (Some a161cc))%I as "#Hi4".
  { by unshelve iApply (instr_intro with "Hinstructions"). }
  iAssert (instr 0x161d0 (Some a161d0))%I as "#Hi5".
  { by unshelve iApply (instr_intro with "Hinstructions"). }
  iAssert (instr 0x10190 (Some a10190))%I as "#Hi6".
  { by unshelve iApply (instr_intro with "Hinstructions"). }
  iAssert (instr 0x10194 (Some a10194))%I as "#Hi7".
  { by unshelve iApply (instr_intro with "Hinstructions"). }
  iAssert (instr 0x10198 (Some a10198))%I as "#Hi8".
  { by unshelve iApply (instr_intro with "Hinstructions"). }
  iAssert (instr 0x1019c (Some a1019c))%I as "#Hi9".
  { by unshelve iApply (instr_intro with "Hinstructions"). }
  iAssert (instr 0x101a0 (Some a101a0))%I as "#Hi10".
  { by unshelve iApply (instr_intro with "Hinstructions"). }
  iAssert (instr_body 0x10190
    (writeFailureOutputTraceSpec (BV 64 0x177c8) (BV 64 6) (BV 64 0x14d24)
      failureMemory writeFailureTraceTail
      ("x6" ↦ᵣ RVal_Bits (BV 64 0x101cc) ∗ True)))%I as "Houtput".
  { iApply write_failure_output_trace_correct.
    Unshelve. all: try apply _.
    unfold IslaTraces.write_failure.instrs.instr_map.
    cbn [skipn].
    repeat rewrite big_sepL_cons.
    rewrite big_sepL_nil. cbn [fst snd].
    iFrame "Hi6 Hi7 Hi8 Hi9 Hi10". }
  iAssert (instr_body 0x161c0 writeFailureTraceEntry)%I as "Hentry".
  { iApply (write_failure_trace_prefix_correct with "[] Houtput").
    simpl. iFrame "Hi1 Hi2 Hi3 Hi4 Hi5". }
  iAssert (instr 0x14d24 None)%I as "#Htrap".
  { by unshelve iApply (instr_intro with "Hinstructions"). }
  iApply (wp_next_instr_pre (BV 64 0x161c0) writeFailureTraceEntry false
    with "[$] []").
  { iExact "Hentry". }
  iExists (BV 64 0), (BV 64 0), (BV 64 0), (BV 64 0).
  iFrame.
  iSplitL.
  { iApply (mmio_range_intro with "Hbacked"); [lia|lia|lia|].
    rewrite /writeFailureInitialMemory !dom_insert_L dom_empty_L.
    set_solver. }
  iSplit; last done.
  iApply (instr_pre_intro_None with "Htrap").
  iIntros "(_&_&_&_&_&_&_&Htail&_ )".
  iExists writeFailureTraceTail. iSplit.
  { iPureIntro. intros snapshot.
    unfold writeFailureTraceTail, scons.
    replace (Z_to_bv 64 85284) with (BV 64 85284) by bv_solve.
    right. exists snapshot, []. split; [reflexivity|left; reflexivity]. }
  iExact "Htail".
Qed.

Lemma write_failure_exports_bytes mstatusBits satp labels threads globalState
    steps firstSnapshot writeSnapshot tailLabels :
  Z.land (bv_unsigned mstatusBits) 0x20000 = 0 ->
  nsteps steps
    (initial_local_state <$> [writeFailureInitialRegs mstatusBits satp],
      {| seq_instrs := writeFailureInstrTable;
         seq_mem := writeFailureInitialMemory |})
    labels (threads, globalState) ->
  labels =
    SWriteMem (BV 64 (machineOutputAddress defaultMap)) (BV 64 0x177c8) firstSnapshot ::
    SWriteMem (BV 64 (machineOutputSizeAddress defaultMap)) (BV 64 6) writeSnapshot ::
    tailLabels ->
  read_mem_list writeSnapshot.(snap_mem) 0x177c8 6 = Some failureMemory.
Proof.
  intros Hstatus Hsteps Hlabels.
  pose proof (write_failure_adequate _ _ _ _ _ _ Hstatus Hsteps) as [_ Hspec].
  rewrite Hlabels in Hspec.
  apply (write_output_events_payload (BV 64 0x177c8) (BV 64 6)
    failureMemory writeFailureTraceTail firstSnapshot writeSnapshot tailLabels).
  exact Hspec.
Qed.

Print Assumptions write_failure_adequate.
Print Assumptions write_failure_exports_bytes.

Definition writeFailureControlFlow : list (Z * Z) := [
  (0x161c0, 0x161c4); (0x161c4, 0x161c8);
  (0x161c8, 0x161cc); (0x161cc, 0x161d0);
  (0x161d0, 0x10190); (0x10190, 0x10194);
  (0x10194, 0x10198); (0x10198, 0x1019c);
  (0x1019c, 0x101a0); (0x101a0, 0x14d24)
].

Definition writeFailureInstructionStep (fromPc toPc : Z) : Prop :=
  List.In (fromPc, toPc) writeFailureControlFlow.

Definition writeFailureModel :
    IslarisContractModel WriteFailureArgs ByteString := {|
  islarisContractAllows := writeFailureAllows;
  islarisContractStep := writeFailureInstructionStep;
  islarisContractResources := fun Sigma HG HT =>
    @write_failure_resources Sigma HG HT
|}.

Definition writeFailureCorrectness : Prop :=
  IslarisContractCorrect 0x161c0 0x14d24 writeFailureModel.

Definition writeFailurePath : list Z := [
  0x161c0; 0x161c4; 0x161c8; 0x161cc; 0x161d0;
  0x10190; 0x10194; 0x10198; 0x1019c; 0x101a0; 0x14d24
].

Lemma writeFailureTermination :
  InstructionPathCertificate writeFailureInstructionStep
    (PcInRanges writeFailureExecutionPcRanges)
    (PcInList writeFailureExitPcs) 0x161c0 10.
Proof.
  exists writeFailurePath. split; first reflexivity. split.
  - unfold writeFailurePath.
    solve_instruction_path ltac:(
      cbn [writeFailureInstructionStep writeFailureControlFlow];
      repeat first [left; reflexivity | right]).
  - split.
    + apply Forall_forall. intros pc Hpc.
      unfold writeFailurePath in Hpc.
      apply elem_of_list_In in Hpc. cbn in Hpc.
      intuition subst pc.
      all: unfold PcInRanges.
      all: first
        [ solve [eexists 0x161c0, 0x161d4; split; [cbn; auto | lia]]
        | solve [eexists 0x10190, 0x101c4; split; [cbn; auto | lia]] ].
    + split.
      * eexists 0x14d24. split; [reflexivity | cbn; auto].
      * split; [reflexivity | lia].
Qed.

Theorem level1WriteFailure :
  exists bound : nat, Nat.lt bound level1ContractFuel /\
    NativeContractAssumption writeFailureCorrectness
      writeFailureInstructionStep
      (PcInRanges writeFailureExecutionPcRanges)
      (PcInList writeFailureExitPcs)
      ZesuSsz.Generated.Level1.writeFailureEntry bound.
Proof.
  exists 10%nat. split.
  - unfold level1ContractFuel.
    apply (Nat.lt_trans _ 160 _); [lia |].
    apply Nat.pow_gt_lin_r. lia.
  - apply nativeContractBridge.
    + intros Sigma HG HT. apply write_failure_state_correct.
    + exact writeFailureTermination.
Qed.
