Require Import ZesuSsz.Automation.AllLegacy.
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessHashesLoop.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessEncoderIntCall.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessSuffixHashes1574cNonzeroCaller.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessSuffixHashes1574cCall.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessSuffixHashesEntryResources.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessSuffixHashes15750EntryHandoff.

Lemma write_success_suffix_hashes_entry_1574c_handoff
    `{!islaG Sigma} `{!threadG}
    (P : iProp Sigma)
    (sp pointer : bv 64) (base : Z)
    (total processed remaining : nat) (bytes : list (bv 8))
    (tail : spec) (Hvalue : Z_to_bv 64 (Z.of_nat (S remaining)) <> BV 64 0) :
  instr 0x1574c (Some IslaTraces.write_success_101.a1574c.a1574c) -∗
  □ instr_pre 0x15d10 zesuEncoderIntCallSpec -∗
  instr 0x15750 (Some IslaTraces.write_success_102.a15750.a15750) -∗
  □ instr_pre 0x15754
    (writeSuccessHashesLoopSpec ((bv_unsigned sp - 16) ↦ₘ? 16 ∗ P)) -∗
  instr_body 0x1574c
    (writeSuccessSuffixHashes1574cNonzeroSpec
      sp (Z_to_bv 64 (Z.of_nat (S remaining)))
      (writeSuccessHashesEvents sp (S remaining) tail)
      (writeSuccessSuffixHashesEntryLoopFrame
        sp pointer base total processed remaining bytes tail P)).
Proof.
  iIntros "H4c #Hint H50 #Hloop".
  iPoseProof (write_success_suffix_hashes_entry_15750_handoff
    P sp pointer base total processed remaining bytes tail Hvalue
    with "H50 Hloop") as "Hbranch".
  iApply (write_success_suffix_hashes_1574c_nonzero_caller
    sp (Z_to_bv 64 (Z.of_nat (S remaining)))
    (writeSuccessHashesEvents sp (S remaining) tail)
    (writeSuccessSuffixHashesEntryLoopFrame
      sp pointer base total processed remaining bytes tail P) Hvalue
    with "H4c Hint Hbranch").
Qed.
