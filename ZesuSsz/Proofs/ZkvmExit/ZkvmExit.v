Require Import ZesuSsz.Automation.All.
Require Import ZesuSsz.Automation.Hooks.
From iris.program_logic Require Import language.
Require Import isla.riscv64.riscv64.
From IslaTraces.zkvm_exit Require Import instrs.
Require Import ZesuMachineMap.Machine.
Require Import ZesuSsz.Contracts.IslarisMachine.
Require Import ZesuSsz.Generated.Level1.
Require Import ZesuSsz.Contracts.Endpoints.
Require Import ZesuSsz.Export.Adequacy.
Require Import ZesuSsz.Export.Snapshots.

Import ZesuSsz.Automation.Hooks.

Definition zkvm_exit_resources `{!islaG Sigma} `{!threadG} :
    IslarisContractResources ZkvmExitArgs unit := {|
  islarisCode :=
    (instr 0x101c4 (Some a101c4) ∗
     instr 0x101c8 (Some a101c8) ∗
     instr 0x101cc (Some a101cc))%I;
  islarisEntry := fun args =>
    (∃ (code old_x5 old_exit_code : bv 64),
      ⌜bv_unsigned code = zkvmExitCode args⌝ ∗
      reg_col zesu_sys_regs ∗
      "x5" ↦ᵣ RVal_Bits old_x5 ∗
      "x10" ↦ᵣ RVal_Bits code ∗
      (machineExitAddress defaultMap) ↦ₘ old_exit_code ∗ True)%I;
  islarisExit := fun args _ =>
    (∃ (code : bv 64),
      ⌜bv_unsigned code = zkvmExitCode args⌝ ∗
      reg_col zesu_sys_regs ∗
      "x5" ↦ᵣ RVal_Bits (BV 64 (mapIoContextAddress defaultMap)) ∗
      "x10" ↦ᵣ RVal_Bits code ∗
      (machineExitAddress defaultMap) ↦ₘ code ∗ True)%I
|}.

Definition zkvmExitAllows (_ : ZkvmExitArgs) (_ : unit) : Prop := True.

Theorem zkvm_exit_state_correct `{!islaG Sigma} `{!threadG} :
  ⊢ IslarisContractSpec 0x101c4 0x101d0
    zkvmExitAllows zkvm_exit_resources.
Proof.
  rewrite /IslarisContractSpec /zkvm_exit_resources /=.
  zesu_block.
  liInst (λ x, x.1ₗ = code).
  zesu_run.
Qed.

Definition zkvmExitFrame : list (bv 8) := [BV 8 0x42].

Definition zkvmExitTrapSpec (code : bv 64) : spec :=
  scons_snap (SInstrTrap (BV 64 0x101d0))
    (fun snapshot =>
      snapshot.(snap_regs) !! "x10" = Some (RVal_Bits code) /\
      read_mem_list snapshot.(snap_mem) 0x20000 1 = Some zkvmExitFrame)
    snil.

Definition zkvmExitTraceSpec (code : bv 64) : spec :=
  scons (SWriteMem (BV 64 (machineExitAddress defaultMap)) code) (zkvmExitTrapSpec code).

Lemma li_zkvm_exit_trap `{!islaG Sigma} `{!threadG} (code : bv 64) :
  (snapshot_reg_resources
      [("x10", RVal_Bits code)] ∗
   snapshot_mem_resources [(0x20000, zkvmExitFrame)] ∗
   arch_pc_reg ↦ᵣ RVal_Bits (BV 64 0x101d0) ∗
   instr 0x101d0 None ∗ ▷ spec_trace (zkvmExitTrapSpec code) ∗ True)%I
  ⊢ WPasm tnil.
Proof.
  iIntros "(Hregisters&Hmemory&HPC&Hinstruction&Hspec&_)".
  have Haccept snapshot
      (HregisterFacts : snapshot_reg_agreement snapshot
        [("x10", RVal_Bits code)])
      (HmemoryFacts : snapshot_mem_agreement snapshot
        [(0x20000, zkvmExitFrame)]) :
      zkvmExitTrapSpec code [SInstrTrap (BV 64 0x101d0) snapshot].
  { unfold zkvmExitTrapSpec, scons_snap.
    right. exists snapshot, []. split.
    - inversion HregisterFacts as [|r1 registers1 Hx10 Hregisters1]; subst.
      inversion HmemoryFacts as [|claim claims Hframe Hclaims]; subst.
      naive_solver.
    - split; [reflexivity|left; reflexivity]. }
  iApply (wp_next_instr_extern (BV 64 0x101d0) (zkvmExitTrapSpec code)
    [("x10", RVal_Bits code)]
    [(0x20000, zkvmExitFrame)] Haccept with
    "Hregisters Hmemory HPC Hinstruction Hspec").
Qed.

Lemma zkvm_exit_trace_iris `{!islaG Sigma} `{!threadG} (code : bv 64) :
  instr 0x101c4 (Some a101c4) -∗
  instr 0x101c8 (Some a101c8) -∗
  instr 0x101cc (Some a101cc) -∗
  instr 0x101d0 None -∗
  reg_col zesu_sys_regs -∗
  "PC" ↦ᵣ RVal_Bits (BV 64 0x101c4) -∗
  "x5" ↦ᵣ RVal_Bits (BV 64 0) -∗
  "x10" ↦ᵣ RVal_Bits code -∗
  0x20000 ↦ₘ∗ zkvmExitFrame -∗
  mmio_range (machineExitAddress defaultMap) 8 -∗
  spec_trace (zkvmExitTraceSpec code) -∗
  WPasm tnil.
Proof.
  iStartProof.
  iIntros "Hi1 Hi2 Hi3 Htrap Hsys HPC Hx5 Hx10 Hframe Hmmio Hspec".
  unshelve (repeat zesu_liAStepNoWrite).
  1-3: prepare_sidecond; try assumption; try bv_solve.
  replace LET2 with (BV 64 (mapIoContextAddress defaultMap)) by bv_solve.
  replace LET3 with (BV 64 0x101d0) by bv_solve.
  replace LET4 with (BV 64 (machineExitAddress defaultMap)) by bv_solve.
  zesu_liAStepGenericWrite.
  Unshelve.
  unshelve (repeat zesu_liAStepBeforeObservable).
  notypeclasses refine (tac_fast_apply
    (li_zkvm_exit_trap code) _).
  Unshelve. repeat liStep.
  Unshelve.
  rewrite /snapshot_reg_resources /snapshot_mem_resources /=.
  all: try iFrame.
Qed.

Print Assumptions zkvm_exit_trace_iris.

Definition zkvmExitInstrTable : gmap addr isla_trace :=
  <[ BV 64 0x101c4 := a101c4 ]> $
  <[ BV 64 0x101c8 := a101c8 ]> $
  <[ BV 64 0x101cc := a101cc ]> $ ∅.

Definition zkvmExitInitialMemory : mem_map :=
  <[ BV 64 0x20000 := BV 8 0x42 ]> ∅.

Definition zkvmExitInitialRegs
    (mstatusBits satp code : bv 64) : reg_map :=
  <[ "PC" := RVal_Bits (BV 64 0x101c4) ]> $
  <[ "x5" := RVal_Bits (BV 64 0) ]> $
  <[ "x10" := RVal_Bits code ]> $
  zesu_ram_sys_regs_map mstatusBits satp.

Lemma zkvm_exit_adequate mstatusBits satp code labels threads globalState steps :
  Z.land (bv_unsigned mstatusBits) 0x20000 = 0 ->
  nsteps steps
    (initial_local_state <$> [zkvmExitInitialRegs mstatusBits satp code],
      {| seq_instrs := zkvmExitInstrTable;
         seq_mem := zkvmExitInitialMemory |})
    labels (threads, globalState) ->
  (forall thread, thread ∈ threads -> not_stuck thread globalState) /\
  zkvmExitTraceSpec code labels.
Proof.
  intros Hstatus Hsteps.
  set Sigma : gFunctors := #[islaΣ].
  apply: (zesu_adequacy Sigma) => //.
  { unfold zkvmExitTraceSpec, scons. naive_solver. }
  iIntros (?) "#Hinstructions #Hbacked Hspec Hmemory /= !>".
  iSplitL => //. iIntros (?).
  rewrite /zkvmExitInitialRegs /zesu_ram_sys_regs_map.
  repeat (rewrite big_sepM_insert; [|by vm_compute]).
  iIntros "(HPC&Hx5&Hx10&Hpmp&Hmis&Hbase&Hsize&Hrombase&Hromsize&
    Hclbase&Hclsize&Hhtif&Hpriv&Hmisa&Hmtvec&Hmstatus&Hsatp&_)".
  iApply wp_asm_thread_ctx. iIntros (?) "Hcontext".
  iMod (zesu_ram_sys_regs_init with "Hcontext [Hpmp Hmis Hbase Hsize
    Hrombase Hromsize Hclbase Hclsize Hhtif Hpriv Hmisa Hmtvec Hmstatus Hsatp]")
    as "[$ Hsystem]"; first done.
  { rewrite /zesu_ram_sys_regs_map.
    repeat (rewrite big_sepM_insert; [|by vm_compute]).
    rewrite big_sepM_empty. iFrame. }
  iModIntro.
  iAssert (0x20000 ↦ₘ∗ zkvmExitFrame)%I with "[Hmemory]" as "Hframe".
  { rewrite /zkvmExitInitialMemory /zkvmExitFrame /zip_with /=.
    iDestruct "Hmemory" as "(Hbyte&_ )".
    have Haddress : bv_unsigned ((BV 64 0x20000) `+Z` 0) = 0x20000 by
      bv_solve.
    iEval (rewrite Haddress) in "Hbyte".
    rewrite mem_mapsto_array_eq /mem_mapsto_array_def.
    iExists 1%N. iSplit; first done.
    iSplit; first (iPureIntro; split; [vm_compute|vm_compute]).
    all: try congruence.
    simpl. iFrame. }
  iAssert (instr 0x101c4 (Some a101c4))%I as "#Hi1".
  { by unshelve iApply (instr_intro with "Hinstructions"). }
  iAssert (instr 0x101c8 (Some a101c8))%I as "#Hi2".
  { by unshelve iApply (instr_intro with "Hinstructions"). }
  iAssert (instr 0x101cc (Some a101cc))%I as "#Hi3".
  { by unshelve iApply (instr_intro with "Hinstructions"). }
  iAssert (instr 0x101d0 None)%I as "#Hitrap".
  { by unshelve iApply (instr_intro with "Hinstructions"). }
  iAssert (mmio_range (machineExitAddress defaultMap) 8)%I as "#Hmmio".
  { iApply (mmio_range_intro with "Hbacked"); [lia|lia|lia|].
    rewrite /zkvmExitInitialMemory dom_insert_L dom_empty_L.
    set_solver. }
  iApply (zkvm_exit_trace_iris code with
    "Hi1 Hi2 Hi3 Hitrap Hsystem HPC Hx5 Hx10 Hframe Hmmio Hspec").
Qed.

Lemma zkvm_exit_exports_snapshot mstatusBits satp code labels threads
    globalState steps writeSnapshot snapshot tailLabels :
  Z.land (bv_unsigned mstatusBits) 0x20000 = 0 ->
  nsteps steps
    (initial_local_state <$> [zkvmExitInitialRegs mstatusBits satp code],
      {| seq_instrs := zkvmExitInstrTable;
         seq_mem := zkvmExitInitialMemory |})
    labels (threads, globalState) ->
  labels =
    SWriteMem (BV 64 (machineExitAddress defaultMap)) code writeSnapshot ::
    SInstrTrap (BV 64 0x101d0) snapshot :: tailLabels ->
  snapshot.(snap_regs) !! "x10" = Some (RVal_Bits code) /\
  read_mem_list snapshot.(snap_mem) 0x20000 1 = Some zkvmExitFrame.
Proof.
  intros Hstatus Hsteps Hlabels.
  pose proof (zkvm_exit_adequate _ _ _ _ _ _ _ Hstatus Hsteps) as [_ Hspec].
  subst labels.
  unfold zkvmExitTraceSpec, zkvmExitTrapSpec, scons, scons_snap in Hspec.
  naive_solver.
Qed.

Print Assumptions zkvm_exit_adequate.
Print Assumptions zkvm_exit_exports_snapshot.

Definition zkvmExitModel : IslarisContractModel ZkvmExitArgs unit := {|
  islarisContractAllows := zkvmExitAllows;
  islarisContractStep := StraightLineInstructionStep;
  islarisContractResources := fun Sigma HG HT =>
    @zkvm_exit_resources Sigma HG HT
|}.

Definition zkvmExitCorrectness : Prop :=
  IslarisContractCorrect 0x101c4 0x101d0 zkvmExitModel.

Definition zkvmExitPath : list Z :=
  [0x101c4; 0x101c8; 0x101cc; 0x101d0].

Lemma zkvmExitTermination :
  InstructionPathCertificate StraightLineInstructionStep ZkvmExitExecutionPc
    (PcInList zkvmExitExitPcs) 0x101c4 3.
Proof.
  exists zkvmExitPath. repeat split.
  - repeat constructor; unfold StraightLineInstructionStep; lia.
  - cbn [zkvmExitPath].
    constructor.
    + unfold ZkvmExitExecutionPc, PcInRanges. split.
      * eexists 0x101c4, 0x101d4. split; [cbn; auto | lia].
      * unfold zkvmExitTerminalPc. lia.
    + constructor.
      * unfold ZkvmExitExecutionPc, PcInRanges. split.
        -- eexists 0x101c4, 0x101d4. split; [cbn; auto | lia].
        -- unfold zkvmExitTerminalPc. lia.
      * constructor.
        -- unfold ZkvmExitExecutionPc, PcInRanges. split.
           ++ eexists 0x101c4, 0x101d4. split; [cbn; auto | lia].
           ++ unfold zkvmExitTerminalPc. lia.
        -- constructor.
  - eexists 0x101d0. split; [reflexivity | cbn; auto].
  - lia.
Qed.

Theorem level1ZkvmExit :
  exists bound : nat, Nat.lt bound level1ContractFuel /\
    NativeContractAssumption zkvmExitCorrectness
      StraightLineInstructionStep ZkvmExitExecutionPc
      (PcInList zkvmExitExitPcs)
      ZesuSsz.Generated.Level1.zkvmExitEntry bound.
Proof.
  exists 3%nat. split.
  - unfold level1ContractFuel.
    apply (Nat.lt_trans _ 160 _); [lia |].
    apply Nat.pow_gt_lin_r. lia.
  - apply nativeContractBridge.
    + intros Sigma HG HT. apply zkvm_exit_state_correct.
    + exact zkvmExitTermination.
Qed.
