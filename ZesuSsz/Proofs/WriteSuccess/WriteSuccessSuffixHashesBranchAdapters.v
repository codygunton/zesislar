Require Import ZesuSsz.Automation.AllLegacy.
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessSuffixHashes15750Branch.

Lemma write_success_suffix_hashes_15750_nonzero_pre_adapter
    `{!islaG Sigma} `{!threadG}
    (value : bv 64) (Q R : iProp Sigma) (Hvalue : value <> BV 64 0) :
  (R -∗ writeSuccessSuffixHashes15750NonzeroState value Q) -∗
  instr_body 0x15750
    (writeSuccessSuffixHashes15750NonzeroState value Q) -∗
  instr_pre 0x15750 R.
Proof.
  iIntros "Hwand Hbody".
  iPoseProof (instr_pre_to_body 0x15750
    (writeSuccessSuffixHashes15750NonzeroState value Q) with "Hbody") as
    "Hpre".
  iApply (instr_pre_wand 0x15750 0x15750 true true
    (writeSuccessSuffixHashes15750NonzeroState value Q) R with "Hpre");
    [done | reflexivity |].
  iExact "Hwand".
Qed.

Lemma write_success_suffix_hashes_15750_zero_pre_adapter
    `{!islaG Sigma} `{!threadG}
    (Q R : iProp Sigma) :
  (R -∗ writeSuccessSuffixHashes15750ZeroState Q) -∗
  instr_body 0x15750
    (writeSuccessSuffixHashes15750ZeroState Q) -∗
  instr_pre 0x15750 R.
Proof.
  iIntros "Hwand Hbody".
  iPoseProof (instr_pre_to_body 0x15750
    (writeSuccessSuffixHashes15750ZeroState Q) with "Hbody") as "Hpre".
  iApply (instr_pre_wand 0x15750 0x15750 true true
    (writeSuccessSuffixHashes15750ZeroState Q) R with "Hpre");
    [done | reflexivity |].
  iExact "Hwand".
Qed.
