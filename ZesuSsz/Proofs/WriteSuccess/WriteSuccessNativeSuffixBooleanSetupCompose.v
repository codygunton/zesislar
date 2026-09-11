Require Import ZesuSsz.Automation.All.
Require Import isla.riscv64.riscv64.
From IslaTraces.write_success_blocks Require Import Index.
Require Import ZesuSsz.Contracts.IslarisCode.
Require Import ZesuSsz.Contracts.IslarisMachine.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessNativeSuffixScalarSetups.

Local Remove Hints subsume_instr_pre'_inst : typeclass_instances.
Local Existing Instance subsume_instr_pre_wand_inst | 1.

Definition writeSuccessSuffixBooleanSetupSource
    `{!islaG Sigma} `{!threadG} (P : iProp Sigma) : iProp Sigma :=
  (reg_col zesu_ram_sys_regs ∗
   "x1" ↦ᵣ: (fun r => ⌜valu_has_shape r (BitsShape 64)⌝) ∗
   "x10" ↦ᵣ: (fun r => ⌜valu_has_shape r (BitsShape 64)⌝) ∗ P)%I.

Global Instance : LithiumUnfold
    (@writeSuccessSuffixBooleanSetupSource) := I.

Lemma write_success_suffix_boolean_15974_to_1597c
    `{!islaG Sigma} `{!threadG} (P : iProp Sigma) :
  instr_lookup_resources IslaTraces.write_success_blocks.Index.lookup -∗
  instr_body 0x1597c
    (writeSuccessSuffixBooleanSetupTarget
      (BV 64 0x15978) (BV 64 1) P) -∗
  instr_body 0x15974 (writeSuccessSuffixBooleanSetupSource P).
Proof.
  iStartProof. iIntros "#Hlookup Hnext".
  iAssert (instr_pre 0x1597c
      (writeSuccessSuffixBooleanSetupTarget
        (BV 64 0x15978) (BV 64 1) P))
    with "[Hnext]" as "HnextPre".
  { iApply instr_pre_to_body. iNext. rewrite instr_pre'_eq. iExact "Hnext". }
  iPoseProof (write_success_suffix_boolean_15974_setup P with "Hlookup")
    as "Hsetup".
  iApply (instr_pre_wand 0x15974 0x15974 false false with "Hsetup");
    [done | done |].
  iIntros "Hsource".
  rewrite /writeSuccessSuffixBooleanSetupSource
    /writeSuccessSuffixBooleanSetupEntry.
  iDestruct "Hsource" as "(Hsys & H1 & H10 & HP)".
  iFrame.
Qed.

Lemma write_success_suffix_boolean_15994_to_1599c
    `{!islaG Sigma} `{!threadG} (P : iProp Sigma) :
  instr_lookup_resources IslaTraces.write_success_blocks.Index.lookup -∗
  instr_body 0x1599c
    (writeSuccessSuffixBooleanSetupTarget
      (BV 64 0x15998) (BV 64 0) P) -∗
  instr_body 0x15994 (writeSuccessSuffixBooleanSetupSource P).
Proof.
  iStartProof. iIntros "#Hlookup Hnext".
  iAssert (instr_pre 0x1599c
      (writeSuccessSuffixBooleanSetupTarget
        (BV 64 0x15998) (BV 64 0) P))
    with "[Hnext]" as "HnextPre".
  { iApply instr_pre_to_body. iNext. rewrite instr_pre'_eq. iExact "Hnext". }
  iPoseProof (write_success_suffix_boolean_15994_setup P with "Hlookup")
    as "Hsetup".
  iApply (instr_pre_wand 0x15994 0x15994 false false with "Hsetup");
    [done | done |].
  iIntros "Hsource".
  rewrite /writeSuccessSuffixBooleanSetupSource
    /writeSuccessSuffixBooleanSetupEntry.
  iDestruct "Hsource" as "(Hsys & H1 & H10 & HP)".
  iFrame.
Qed.
