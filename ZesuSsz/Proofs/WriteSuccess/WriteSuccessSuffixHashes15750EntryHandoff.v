Require Import ZesuSsz.Automation.AllLegacy.
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessHashesLoop.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessSuffixHashes15750Branch.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessSuffixHashesCallContinuations.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessSuffixHashesEntryResources.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessSuffixHashes15754EntryHandoff.

Lemma write_success_suffix_hashes_entry_15750_handoff
    `{!islaG Sigma} `{!threadG}
    (P : iProp Sigma)
    (sp pointer : bv 64) (base : Z)
    (total processed remaining : nat) (bytes : list (bv 8))
    (tail : spec) (Hvalue : Z_to_bv 64 (Z.of_nat (S remaining)) <> BV 64 0) :
  instr 0x15750 (Some IslaTraces.write_success_102.a15750.a15750) -∗
  □ instr_pre 0x15754
    (writeSuccessHashesLoopSpec ((bv_unsigned sp - 16) ↦ₘ? 16 ∗ P)) -∗
  instr_body 0x15750
    (writeSuccessSuffixHashes15750NonzeroState
      (Z_to_bv 64 (Z.of_nat (S remaining)))
      (writeSuccessSuffixHashes15750NonzeroQ
        sp (Z_to_bv 64 (Z.of_nat (S remaining)))
        (writeSuccessHashesEvents sp (S remaining) tail)
        (writeSuccessSuffixHashesEntryLoopFrame
          sp pointer base total processed remaining bytes tail P)))%I.
Proof.
  iIntros "H50 #Hloop".
  iPoseProof (write_success_suffix_hashes_entry_15754_handoff
    P sp pointer base total processed remaining bytes tail with "Hloop")
    as "HbranchPre".
  iApply (write_success_suffix_hashes_15750_nonzero_state
    (Z_to_bv 64 (Z.of_nat (S remaining)))
    (writeSuccessSuffixHashes15750NonzeroQ
      sp (Z_to_bv 64 (Z.of_nat (S remaining)))
      (writeSuccessHashesEvents sp (S remaining) tail)
      (writeSuccessSuffixHashesEntryLoopFrame
        sp pointer base total processed remaining bytes tail P)) Hvalue
    with "H50 HbranchPre").
Qed.
