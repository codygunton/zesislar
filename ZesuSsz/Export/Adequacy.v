Require Import ZesuSsz.Automation.All.
From iris.program_logic Require Import language.
From isla Require Import adequacy.
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Contracts.IslarisMachine.
Require Import ZesuSsz.Export.Executor.

Definition zesu_ram_sys_regs_map (mstatusBits satp : bv 64) : reg_map :=
  <[ "rv_enable_pmp" := RVal_Bool (mapEnablePmp defaultMap) ]> $
  <[ "rv_enable_misaligned_access" := RVal_Bool (mapEnableMisalignedAccess defaultMap) ]> $
  <[ "rv_ram_base" := RVal_Bits (BV 64 (mapRamBase defaultMap)) ]> $
  <[ "rv_ram_size" := RVal_Bits (BV 64 (mapRamSize defaultMap)) ]> $
  <[ "rv_rom_base" := RVal_Bits (BV 64 (mapRomBase defaultMap)) ]> $
  <[ "rv_rom_size" := RVal_Bits (BV 64 (mapRomSize defaultMap)) ]> $
  <[ "rv_clint_base" := RVal_Bits (BV 64 (mapClintBase defaultMap)) ]> $
  <[ "rv_clint_size" := RVal_Bits (BV 64 (mapClintSize defaultMap)) ]> $
  <[ "rv_htif_tohost" := RVal_Bits (BV 64 (mapHtifTohost defaultMap)) ]> $
  <[ "cur_privilege" := RVal_Enum (mapPrivilege defaultMap) ]> $
  <[ "misa" := RegVal_Struct [
      ("bits", RVal_Bits (BV 64 (mapMisa defaultMap)))] ]> $
  <[ "mtvec" := RegVal_Struct [("bits", RVal_Bits (BV 64 (mapMtvec defaultMap)))] ]> $
  <[ "mstatus" := RegVal_Struct [("bits", RVal_Bits mstatusBits)] ]> $
  <[ "satp" := RVal_Bits satp ]> $ ∅.

Section sys_regs.
  Context `{!islaG Sigma} `{!threadG}.

  Lemma zesu_ram_sys_regs_init mstatusBits satp regs :
    Z.land (bv_unsigned mstatusBits) (mapMstatusMask defaultMap) = mapMstatusValue defaultMap ->
    regs_ctx regs -∗
    ([∗ map] register ↦ value ∈ zesu_ram_sys_regs_map mstatusBits satp,
      register ↦ᵣ value) ==∗
    regs_ctx regs ∗ reg_col zesu_ram_sys_regs.
  Proof.
    move => Hstatus.
    repeat (rewrite big_sepM_insert; [|by vm_compute]).
    iIntros "Hctx Hregisters".
    simpl. iModIntro.
    rewrite -(right_id True%I _ (reg_col zesu_ram_sys_regs)).
    iRevert "Hregisters".
    repeat liAStep; liShow.
  Qed.
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
