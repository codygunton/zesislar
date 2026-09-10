Require Import ZesuSsz.Automation.All.
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessHashesLoop.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessEvents.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessEncoderIntCall.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessSuffixHashes15744Compose.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessSuffixHashes15744Raw.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessSuffixHashes15748Compose.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessSuffixHashesEntryResources.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessSuffixHashes1574cEntryHandoff.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessSuffixHashes15748EntryPreAdapter.

Lemma write_success_suffix_hashes_entry_resource_nonzero
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
      (Z_to_bv 64 (Z.of_nat (S remaining))) remaining tail
      (writeSuccessSuffixHashesEntryFrame
        sp pointer base total processed remaining bytes tail P)).
Proof.
  iIntros "H44 H48 H4c #Hint H50 #Hloop".
  have Hvalue :
      Z_to_bv 64 (Z.of_nat (S remaining)) <> BV 64 0.
  { apply write_success_suffix_hashes_entry_count_nonzero.
    exact HremainingBound. }
  iPoseProof (write_success_suffix_hashes_entry_1574c_handoff
    P sp pointer base total processed remaining bytes tail Hvalue
    with "H4c Hint H50 Hloop") as "H4cBody".
  iPoseProof (write_success_suffix_hashes_15748_nonzero_compose
    sp (Z_to_bv 64 (Z.of_nat (S remaining)))
    (writeSuccessHashesEvents sp (S remaining) tail)
    (writeSuccessSuffixHashesEntryLoopFrame
      sp pointer base total processed remaining bytes tail P)
    with "H48 H4cBody") as "H48Body".
  iPoseProof (instr_pre_to_body 0x15748
    (writeSuccessSuffixHashes15748NonzeroSpec
      sp (Z_to_bv 64 (Z.of_nat (S remaining)))
      (writeSuccessHashesEvents sp (S remaining) tail)
      (writeSuccessSuffixHashesEntryLoopFrame
        sp pointer base total processed remaining bytes tail P))
    with "H48Body") as "H48Pre".
  iPoseProof (write_success_suffix_hashes_15748_entry_pre_adapter
    P sp pointer base total processed remaining bytes tail with "H48Pre")
    as "H48SourcePre".
  iPoseProof (write_success_suffix_hashes_15744_raw
    (fun _ =>
      ((bv_unsigned sp - 16) ↦ₘ? 16 ∗
       mmio_range 0x2401a0c0 16 ∗
       spec_trace
         (writeOutputEvents (sp - BV 64 16)%bv (BV 64 8)
           (writeSuccessHashesEvents sp (S remaining) tail)) ∗
       writeSuccessSuffixHashesEntryFrame
         sp pointer base total processed remaining bytes tail P)%I)
    with "H44") as "Hraw44".
  iApply (instr_pre_wand 0x15744 0x15744 false false with "Hraw44");
    [done | reflexivity |].
  iIntros "Htarget".
  iEval (rewrite /writeSuccessSuffixHashesEntryPostSpec) in "Htarget".
  iDestruct "Htarget" as
    "(Hsys & H8 & H10Shape & Hstack & Hmmio & Htrace & Hframe & _)".
  iEval (rewrite /writeSuccessSuffixHashes15744Spec).
  iExists (Z_to_bv 64 (Z.of_nat (S remaining))).
  iFrame "Hsys H8 H10Shape Hstack Hmmio Htrace Hframe H48SourcePre".
Qed.
