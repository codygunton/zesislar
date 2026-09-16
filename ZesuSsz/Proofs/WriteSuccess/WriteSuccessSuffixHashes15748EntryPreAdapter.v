Require Import ZesuSsz.Automation.AllLegacy.
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessSuffixHashes15748Compose.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessSuffixHashes15748EntryResourceAdapter.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessSuffixHashesEntryResources.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessEvents.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessHashesLoop.

Lemma write_success_suffix_hashes_15748_entry_pre_adapter
    `{!islaG Sigma} `{!threadG}
    (P : iProp Sigma)
    (sp pointer : bv 64) (base : Z)
    (total processed remaining : nat) (bytes : list (bv 8))
    (tail : spec) :
  instr_pre 0x15748
    (writeSuccessSuffixHashes15748NonzeroSpec
      sp (Z_to_bv 64 (Z.of_nat (S remaining)))
      (writeSuccessHashesEvents sp (S remaining) tail)
      (writeSuccessSuffixHashesEntryLoopFrame
        sp pointer base total processed remaining bytes tail P)) -∗
  instr_pre 0x15748
    (writeSuccessSuffixHashes15748EntrySource
      P sp pointer base total processed remaining bytes tail).
Proof.
  iIntros "Htarget".
  iApply (instr_pre_wand 0x15748 0x15748 true true with "Htarget");
    [done | reflexivity |].
  iIntros "Hsource".
  iApply (write_success_suffix_hashes_15748_entry_resource_adapter
    P sp pointer base total processed remaining bytes tail).
  iExact "Hsource".
Qed.
