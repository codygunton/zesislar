Require Import ZesuSsz.Automation.All.
From iris.program_logic Require Import language.
From isla Require Import adequacy.
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Contracts.IslarisMachine.

Definition zesu_zero_sys_regs_map (mstatusBits satp : bv 64) : reg_map :=
  <[ "rv_enable_pmp" := RVal_Bool false ]> $
  <[ "rv_enable_misaligned_access" := RVal_Bool false ]> $
  <[ "rv_ram_base" := RVal_Bits (BV 64 0) ]> $
  <[ "rv_ram_size" := RVal_Bits (BV 64 0x40000000) ]> $
  <[ "rv_rom_base" := RVal_Bits (BV 64 0x1000) ]> $
  <[ "rv_rom_size" := RVal_Bits (BV 64 0x100) ]> $
  <[ "rv_clint_base" := RVal_Bits (BV 64 0x2000000) ]> $
  <[ "rv_clint_size" := RVal_Bits (BV 64 0xc0000) ]> $
  <[ "rv_htif_tohost" := RVal_Bits (BV 64 0x40001000) ]> $
  <[ "cur_privilege" := RVal_Enum "Machine" ]> $
  <[ "misa" := RegVal_Struct [
      ("bits", RVal_Bits (BV 64 0x8000000000001100))] ]> $
  <[ "mstatus" := RegVal_Struct [("bits", RVal_Bits mstatusBits)] ]> $
  <[ "satp" := RVal_Bits satp ]> $ ∅.

Definition zesu_ram_sys_regs_map (mstatusBits satp : bv 64) : reg_map :=
  <[ "rv_enable_pmp" := RVal_Bool false ]> $
  <[ "rv_enable_misaligned_access" := RVal_Bool false ]> $
  <[ "rv_ram_base" := RVal_Bits (BV 64 0x20000000) ]> $
  <[ "rv_ram_size" := RVal_Bits (BV 64 0x20000000) ]> $
  <[ "rv_rom_base" := RVal_Bits (BV 64 0x1000) ]> $
  <[ "rv_rom_size" := RVal_Bits (BV 64 0x100) ]> $
  <[ "rv_clint_base" := RVal_Bits (BV 64 0x2000000) ]> $
  <[ "rv_clint_size" := RVal_Bits (BV 64 0xc0000) ]> $
  <[ "rv_htif_tohost" := RVal_Bits (BV 64 0x40001000) ]> $
  <[ "cur_privilege" := RVal_Enum "Machine" ]> $
  <[ "misa" := RegVal_Struct [
      ("bits", RVal_Bits (BV 64 0x8000000000001100))] ]> $
  <[ "mtvec" := RegVal_Struct [("bits", RVal_Bits (BV 64 0))] ]> $
  <[ "mstatus" := RegVal_Struct [("bits", RVal_Bits mstatusBits)] ]> $
  <[ "satp" := RVal_Bits satp ]> $ ∅.

Section zero_sys_regs.
  Context `{!islaG Sigma} `{!threadG}.

  Lemma zesu_zero_sys_regs_init mstatusBits satp regs :
    Z.land (bv_unsigned mstatusBits) 0x20000 = 0 ->
    regs_ctx regs -∗
    ([∗ map] register ↦ value ∈ zesu_zero_sys_regs_map mstatusBits satp,
      register ↦ᵣ value) ==∗
    regs_ctx regs ∗ reg_col zesu_zero_based_sys_regs.
  Proof.
    move => Hstatus.
    repeat (rewrite big_sepM_insert; [|by vm_compute]).
    iIntros "Hctx Hregisters".
    simpl. iModIntro.
    rewrite -(right_id True%I _ (reg_col zesu_zero_based_sys_regs)).
    iRevert "Hregisters".
    repeat liAStep; liShow.
  Qed.

  Lemma zesu_ram_sys_regs_init mstatusBits satp regs :
    Z.land (bv_unsigned mstatusBits) 0x20000 = 0 ->
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
End zero_sys_regs.

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
Print Assumptions zesu_zero_sys_regs_init.
Print Assumptions zesu_ram_sys_regs_init.
