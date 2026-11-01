Require Import ZesuSsz.Automation.All.
From iris.program_logic Require Import language.
From isla Require Import adequacy.
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Contracts.IslarisMachine.
Require Import ZesuSsz.Export.Executor.

Definition machine_static_sys_regs_map (machine : MachineMap) (mstatusBits satp : bv 64) : reg_map :=
  <[ "rv_enable_pmp" := RVal_Bool (mapEnablePmp machine) ]> $
  <[ "rv_enable_misaligned_access" := RVal_Bool (mapEnableMisalignedAccess machine) ]> $
  <[ "rv_ram_base" := RVal_Bits (Z_to_bv 64 (mapRamBase machine)) ]> $
  <[ "rv_ram_size" := RVal_Bits (Z_to_bv 64 (mapRamSize machine)) ]> $
  <[ "rv_rom_base" := RVal_Bits (Z_to_bv 64 (mapRomBase machine)) ]> $
  <[ "rv_rom_size" := RVal_Bits (Z_to_bv 64 (mapRomSize machine)) ]> $
  <[ "rv_clint_base" := RVal_Bits (Z_to_bv 64 (mapClintBase machine)) ]> $
  <[ "rv_clint_size" := RVal_Bits (Z_to_bv 64 (mapClintSize machine)) ]> $
  <[ "rv_htif_tohost" := RVal_Bits (Z_to_bv 64 (mapHtifTohost machine)) ]> $
  <[ "cur_privilege" := RVal_Enum (mapPrivilege machine) ]> $
  <[ "misa" := RegVal_Struct [
      ("bits", RVal_Bits (Z_to_bv 64 (mapMisa machine)))] ]> $
  <[ "mtvec" := RegVal_Struct [("bits", RVal_Bits (Z_to_bv 64 (mapMtvec machine)))] ]> $
  <[ "medeleg" := RegVal_Struct [("bits", RVal_Bits (Z_to_bv 64 0))] ]> $
  <[ "mideleg" := RegVal_Struct [("bits", RVal_Bits (Z_to_bv 64 0))] ]> $
  <[ "mstatus" := RegVal_Struct [("bits", RVal_Bits mstatusBits)] ]> $
  <[ "satp" := RVal_Bits satp ]> $ ∅.

(** The stock loader establishes inputEnd = input base + 8 + input length
    and freeInput = 0. These dynamic values remain explicit resources.
    This initialization lemma does not prove the loader behavior. *)
Definition machine_ram_sys_regs_map (machine : MachineMap)
    (mstatusBits satp inputEnd freeInput : bv 64) : reg_map :=
  let registers := machine_static_sys_regs_map machine mstatusBits satp in
  if mapZiskPlatform machine then
    <["zisk_input_end" := RVal_Bits inputEnd]>
      (<["zisk_free_input" := RVal_Bits freeInput]> registers)
  else registers.

Definition zesu_ram_sys_regs_map := machine_ram_sys_regs_map defaultMap.

Set Default Proof Using "Type".

Section sys_regs.
  Context `{!islaG Sigma} `{!threadG}.

  Lemma machine_ram_sys_regs_init machine mstatusBits satp inputEnd freeInput regs :
    Z.land (bv_unsigned mstatusBits) (mapMstatusMask machine) = mapMstatusValue machine ->
    regs_ctx regs -∗
    ([∗ map] register ↦ value ∈ machine_ram_sys_regs_map machine mstatusBits satp inputEnd freeInput,
      register ↦ᵣ value) ==∗
    regs_ctx regs ∗ reg_col (machine_sys_regs machine).
  Proof.
    move => Hstatus.
    unfold machine_ram_sys_regs_map.
    destruct (mapZiskPlatform machine) eqn:Hplatform;
    repeat (rewrite big_sepM_insert; [|by vm_compute]).
    all: iIntros "Hctx Hregisters".
    all: simpl; iModIntro.
    all: rewrite -(right_id True%I _ (reg_col (machine_sys_regs machine))).
    all: iRevert "Hregisters".
    all: unfold machine_sys_regs; rewrite Hplatform.
    all: cbn [machine_static_sys_regs]; repeat liAStep; liShow.
  Qed.
  Lemma zesu_ram_sys_regs_init mstatusBits satp inputEnd freeInput regs :
    Z.land (bv_unsigned mstatusBits) (mapMstatusMask defaultMap) = mapMstatusValue defaultMap ->
    regs_ctx regs -∗
    ([∗ map] register ↦ value ∈ zesu_ram_sys_regs_map mstatusBits satp inputEnd freeInput,
      register ↦ᵣ value) ==∗
    regs_ctx regs ∗ reg_col zesu_ram_sys_regs.
  Proof. apply machine_ram_sys_regs_init. Qed.
End sys_regs.

Lemma zesu_adequacy Sigma `{!Arch} `{!islaPreG Sigma}
    (instrs : gmap addr isla_trace) (mem : mem_map) (regs : list reg_map)
    (Pks : spec) t2 sigma2 ks n :
  Pks [] ->
  (forall {HG : islaG Sigma},
    instr_table instrs -∗ backed_mem (dom mem) -∗ spec_trace Pks -∗
    ([∗ map] address ↦ value ∈ mem, bv_unsigned address ↦ₘ value)
    ={⊤}=∗
    [∗ list] registerMap ∈ regs, ∀ (_ : threadG),
      ([∗ map] register ↦ value ∈ registerMap, register ↦ᵣ value) -∗
      WPasm tnil) ->
  nsteps n
    (initial_local_state <$> regs,
      {| seq_instrs := instrs; seq_mem := mem |})
    ks (t2, sigma2) ->
  (forall thread, thread ∈ t2 -> not_stuck thread sigma2) /\ Pks ks.
Proof. exact (isla_adequacy Sigma instrs mem regs Pks t2 sigma2 ks n). Qed.

Print Assumptions zesu_adequacy.
Print Assumptions zesu_ram_sys_regs_init.

(** Compose completed caller regions through the named decoder boundary. *)
Lemma completed_run_through_decoder
    (Outcome : Type)
    (entry : list seq_label -> seq_local_state -> seq_global_state -> Prop)
    (exit : list seq_label -> Outcome -> seq_local_state -> seq_global_state -> Prop)
    (emitted before : list seq_label)
    (instructions : nat) (start boundary : seq_local_state)
    (memory decoderMemory : seq_global_state)
    (terminal : list seq_label -> seq_local_state -> seq_global_state -> Prop)
    (Hdecode : forall prefix localState globalState,
      entry prefix localState globalState ->
      exists steps labels returned returnedMemory outcome,
        @nsteps isla_lang steps ([localState], globalState)
          labels ([returned], returnedMemory) /\
        exit (prefix ++ labels) outcome returned returnedMemory) :
  CompletedInstructionRun instructions start memory before boundary decoderMemory ->
  entry (emitted ++ before) boundary decoderMemory ->
  (forall decoderLabels outcome returned returnedMemory,
    exit ((emitted ++ before) ++ decoderLabels) outcome returned returnedMemory ->
    exists count after finish finalMemory,
      CompletedInstructionRun count returned returnedMemory after finish finalMemory /\
      terminal (((emitted ++ before) ++ decoderLabels) ++ after) finish finalMemory) ->
  exists steps labels finish finalMemory,
    @nsteps isla_lang steps ([start], memory) labels ([finish], finalMemory) /\
    terminal (emitted ++ labels) finish finalMemory.
Proof.
  intros Hbefore Hentry Hcontinue.
  destruct (Hdecode (emitted ++ before) boundary decoderMemory Hentry)
    as [decoderSteps [decoderLabels [returned [returnedMemory [outcome [Hrun Hexit]]]]]].
  destruct (Hcontinue decoderLabels outcome returned returnedMemory Hexit)
    as [count [after [finish [finalMemory [Hafter Hterminal]]]]].
  destruct (completed_run_nsteps _ _ _ _ _ _ Hbefore) as [first Hfirst].
  destruct (completed_run_nsteps _ _ _ _ _ _ Hafter) as [last Hlast].
  exists (first + (decoderSteps + last))%nat,
    (before ++ (decoderLabels ++ after)), finish, finalMemory.
  split.
  - eapply executor_nsteps_append; [exact Hfirst|].
    eapply executor_nsteps_append; eassumption.
  - rewrite !app_assoc. exact Hterminal.
Qed.
Print Assumptions completed_run_through_decoder.
