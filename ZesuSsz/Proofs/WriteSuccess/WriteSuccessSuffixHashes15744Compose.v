Require Import ZesuSsz.Automation.AllLegacy.
Require Import isla.riscv64.riscv64.
Require Import InstrSpecs.Machine.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessSuffixHashes15744Raw.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessSuffixHashes15748Compose.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessSuffixHashesQContinuations.

Definition writeSuccessSuffixHashes15744NonzeroSpec
    `{!islaG Sigma} `{!threadG}
    (sp value : bv 64) (tail : spec) (Q : iProp Sigma) : iProp Sigma :=
  (reg_col zesu_ram_sys_regs ∗
   "x8" ↦ᵣ RVal_Bits value ∗
   "x10" ↦ᵣ: (fun r10 => ⌜valu_has_shape r10 (BitsShape 64)⌝) ∗
   writeSuccessSuffixHashes15744Q sp value tail
     (writeSuccessSuffixHashes15748Q sp value tail Q) ∗ True)%I.

Global Instance : LithiumUnfold
  (@writeSuccessSuffixHashes15744NonzeroSpec) := I.

Lemma write_success_suffix_hashes_15744_nonzero_adapter
    `{!islaG Sigma} `{!threadG}
    (sp value : bv 64) (tail : spec) (Q : iProp Sigma) :
  (reg_col zesu_ram_sys_regs ∗
   "x8" ↦ᵣ RVal_Bits value ∗
   "x10" ↦ᵣ RVal_Bits value ∗
   writeSuccessSuffixHashes15744Q sp value tail
     (writeSuccessSuffixHashes15748Q sp value tail Q)) -∗
  writeSuccessSuffixHashes15748NonzeroSpec sp value tail Q.
Proof.
  rewrite /writeSuccessSuffixHashes15748NonzeroSpec.
  iIntros "(Hsys & H8 & H10 & Hrest)".
  iPoseProof (write_success_suffix_hashes_q15744
    sp value tail Q with "[Hsys H8 H10 Hrest]") as "Hq".
  - iFrame.
  - iDestruct "Hq" as "(Hqsys & Hq1 & Hqrest)".
    iFrame "Hqsys Hq1 Hqrest".
Qed.

Lemma write_success_suffix_hashes_15744_nonzero_compose
    `{!islaG Sigma} `{!threadG}
    (sp value : bv 64) (tail : spec) (Q : iProp Sigma) :
  instr 0x15744 (Some IslaTraces.write_success_101.a15744.a15744) -∗
  instr_body 0x15748
    (writeSuccessSuffixHashes15748NonzeroSpec sp value tail Q) -∗
  instr_body 0x15744
    (writeSuccessSuffixHashes15744NonzeroSpec sp value tail Q).
Proof. move => *. zesu_block. Qed.
