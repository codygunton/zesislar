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
Proof.
  iIntros "#Hlookup Hnext".
  rewrite instr_pre'_eq. iIntros "(Hsys & H1 & HF)".
  iEval (rewrite -instr_pre'_eq) in "Hnext".
  iPoseProof (write_success_transactions_instr_150f8 with "Hlookup")
    as "#Hinstr".
  iPoseProof (IslaTraces.write_success_35.a150f8_spec.a150f8_spec 0x150f8
    with "Hinstr") as "Hbody".
  iEval (rewrite instr_pre'_eq) in "Hbody".
  iApply "Hbody".
  rewrite /InstrSpecs.Specs.zesu_jalr_same_spec.
  iExists (BV 64 0x160f4). iFrame "Hsys H1".
  iSplit; first (iPureIntro; bv_solve).
  iApply (instr_pre_wand 0x15bc8 _ true true with "Hnext");
    [done | bv_solve |].
  iIntros "(Hsys & H1 & _)". iFrame "Hsys HF".
  replace (BV 64 0x150fc) with (Z_to_bv 64 (0x150f8 + 4)) by bv_solve.
  iExact "H1".
Qed.
