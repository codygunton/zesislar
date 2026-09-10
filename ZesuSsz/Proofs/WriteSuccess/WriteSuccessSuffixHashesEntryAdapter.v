Require Import ZesuSsz.Automation.All.
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessHashesLoop.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessEncoderIntCall.
Require Export ZesuSsz.Proofs.WriteSuccess.WriteSuccessSuffixHashesEntryResources.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessSuffixHashesEntryResourceFinal.

Lemma write_success_suffix_hashes_entry_nonzero
    `{!islaG Sigma} `{!threadG}
    (P : iProp Sigma)
    (sp pointer : bv 64) (base : Z)
    (total processed remaining : nat) (bytes : list (bv 8))
    (tail : spec) (HremainingBound : (S remaining < 2 ^ 64)%nat) :
  instr 0x15744 (Some IslaTraces.write_success_101.a15744.a15744) -∗
  instr 0x15748 (Some IslaTraces.write_success_101.a15748.a15748) -∗
  instr 0x1574c (Some IslaTraces.write_success_101.a1574c.a1574c) -∗
  □ instr_pre 0x15d10 zesuEncoderIntCallSpec -∗
  instr 0x15750 (Some IslaTraces.write_success_102.a15750.a15750) -∗
  □ instr_pre 0x15754
    (writeSuccessHashesLoopSpec ((bv_unsigned sp - 16) ↦ₘ? 16 ∗ P)) -∗
  instr_body 0x15744
    (writeSuccessSuffixHashesEntryPostSpec sp
      (Z_to_bv 64 (Z.of_nat (S remaining)))
      remaining tail
      (writeSuccessSuffixHashesEntryFrame
        sp pointer base total processed remaining bytes tail P)).
Proof.
  iIntros "H44 H48 H4c Hint H50 Hloop".
  iApply (write_success_suffix_hashes_entry_resource_nonzero
    P sp pointer base total processed remaining bytes tail HremainingBound with
    "H44 H48 H4c Hint H50 Hloop").
Qed.
