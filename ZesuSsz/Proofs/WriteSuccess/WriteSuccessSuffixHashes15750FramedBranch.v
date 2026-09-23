Require Import ZesuSsz.Automation.AllLegacy.
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessSuffixHashes15750Branch.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessSuffixHashes1574cCall.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessSuffixHashesCallContinuations.

Lemma write_success_suffix_hashes_15750_nonzero_framed
    `{!islaG Sigma} `{!threadG}
    (sp value : bv 64) (tail : spec) (Q : iProp Sigma)
    (Hvalue : value <> BV 64 0) :
  instr_body 0x15750
    (writeSuccessSuffixHashes15750NonzeroState value
      (writeSuccessSuffixHashes15750NonzeroQ sp value tail Q)) -∗
  writeSuccessSuffixHashes1574cCallPost sp value tail -∗
  "x8" ↦ᵣ RVal_Bits value -∗
  Q -∗
  instr_pre 0x15750
    (writeSuccessSuffixHashes1574cCallPost sp value tail ∗
     "x8" ↦ᵣ RVal_Bits value ∗ Q).
Proof. move => *. zesu_block. Qed.
