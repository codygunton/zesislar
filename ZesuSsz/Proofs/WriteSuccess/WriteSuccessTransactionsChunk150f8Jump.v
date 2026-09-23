Require Import ZesuSsz.Automation.AllLegacy.
From Coq Require Import ZArith.ZArith.
Require Import isla.riscv64.riscv64.
From IslaTraces.write_success_blocks Require Import Index.
Require Import ZesuSsz.Contracts.IslarisCode.
Require Import ZesuSsz.Contracts.IslarisMachine.

Local Remove Hints subsume_instr_pre'_inst : typeclass_instances.
Local Existing Instance subsume_instr_pre_wand_inst | 1.

Lemma write_success_transactions_instr_150f8
    `{!islaG Sigma} `{!threadG} :
  instr_lookup_resources IslaTraces.write_success_blocks.Index.lookup -∗
  instr 0x150f8 (Some IslaTraces.write_success_35.a150f8.a150f8).
Proof.
  rewrite /InstrSpecs.Lookup.instr_lookup_resources.
  iIntros "#Hlookup".
  iApply ("Hlookup" $! 0x150f8).
  iPureIntro. rewrite IslaTraces.write_success_blocks.Index.lookup_a150f8.
  eauto.
Qed.

Lemma write_success_transactions_chunk_150f8_jump
    `{!islaG Sigma} `{!threadG} (F : iProp Sigma) :
  instr_lookup_resources IslaTraces.write_success_blocks.Index.lookup -∗
  instr_pre 0x15bc8
    (reg_col zesu_ram_sys_regs ∗
     "x1" ↦ᵣ RVal_Bits (BV 64 0x150fc) ∗ F) -∗
  instr_body 0x150f8
    (reg_col zesu_ram_sys_regs ∗
     "x1" ↦ᵣ RVal_Bits (BV 64 0x160f4) ∗ F).
Proof. move => *. zesu_block. Qed.
