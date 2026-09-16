Require Import ZesuSsz.Automation.AllLegacy.
Require Import isla.riscv64.riscv64.
Require Import InstrSpecs.Machine.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessSuffixHashes15748Raw.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessSuffixHashes1574cNonzeroCaller.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessSuffixHashesQContinuations.

Definition writeSuccessSuffixHashes15748NonzeroSpec
    `{!islaG Sigma} `{!threadG}
    (sp value : bv 64) (tail : spec) (Q : iProp Sigma) : iProp Sigma :=
  (reg_col zesu_ram_sys_regs ∗
   "x1" ↦ᵣ: (fun r1 => ⌜valu_has_shape r1 (BitsShape 64)⌝) ∗
   writeSuccessSuffixHashes15748Q sp value tail Q ∗ True)%I.

Global Instance : LithiumUnfold
  (@writeSuccessSuffixHashes15748NonzeroSpec) := I.

Lemma write_success_suffix_hashes_15748_nonzero_adapter
    `{!islaG Sigma} `{!threadG}
    (sp value : bv 64) (tail : spec) (Q : iProp Sigma) :
  (reg_col zesu_ram_sys_regs ∗
   "x1" ↦ᵣ RVal_Bits (BV 64 0x15748) ∗
   writeSuccessSuffixHashes15748Q sp value tail Q) -∗
  writeSuccessSuffixHashes1574cNonzeroSpec sp value tail Q.
Proof.
  iIntros "(Hsys & H1 & Hrest)".
  rewrite /writeSuccessSuffixHashes15748Q.
  iDestruct "Hrest" as
    "(H8 & H2 & H5 & H10 & H11 & Hstack & Hmmio & Htrace &
      %Halign & %Hmin & %Hmax & HQ)".
  rewrite /writeSuccessSuffixHashes1574cNonzeroSpec.
  iFrame "Hsys H1 H2 H5 H8 H10 H11 Hstack Hmmio Htrace HQ".
  iPureIntro; repeat split; assumption.
Qed.

Lemma write_success_suffix_hashes_15748_nonzero_compose
    `{!islaG Sigma} `{!threadG}
    (sp value : bv 64) (tail : spec) (Q : iProp Sigma) :
  instr 0x15748 (Some IslaTraces.write_success_101.a15748.a15748) -∗
  instr_body 0x1574c
    (writeSuccessSuffixHashes1574cNonzeroSpec sp value tail Q) -∗
  instr_body 0x15748
    (writeSuccessSuffixHashes15748NonzeroSpec sp value tail Q).
Proof.
  iIntros "Hinstr Hcaller".
  iAssert (instr_pre 0x1574c
    (writeSuccessSuffixHashes1574cNonzeroSpec sp value tail Q))%I
    with "[Hcaller]" as "HcallerPre".
  { iApply instr_pre_to_body. iNext. iExact "Hcaller". }
  iPoseProof (write_success_suffix_hashes_15748_raw
    (writeSuccessSuffixHashes15748Q sp value tail Q)
    with "Hinstr") as "Hraw".
  iApply (instr_pre_wand 0x15748 0x15748 false false with "Hraw");
    [done | reflexivity |].
  iIntros "Htarget".
  iEval (rewrite /writeSuccessSuffixHashes15748NonzeroSpec) in "Htarget".
  iDestruct "Htarget" as "(Hsys & H1 & Hrest & _)".
  iEval (rewrite /writeSuccessSuffixHashes15748Spec).
  iFrame "Hsys H1 Hrest".
  iSplitL.
  { iApply (instr_pre_wand with "HcallerPre");
      [done | reflexivity |].
    iIntros "Hstate".
    iApply (write_success_suffix_hashes_15748_nonzero_adapter
      sp value tail Q).
    iExact "Hstate". }
  done.
Qed.
