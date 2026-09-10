Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessHashesLoop.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessSuffixHashes15750Branch.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessSuffixHashesCallContinuations.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessSuffixHashesEntryResources.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessSuffixHashesSourceWords.

Lemma write_success_suffix_hashes_entry_15754_handoff
    `{!islaG Sigma} `{!threadG}
    (P : iProp Sigma)
    (sp pointer : bv 64) (base : Z)
    (total processed remaining : nat) (bytes : list (bv 8))
    (tail : spec) :
  □ instr_pre 0x15754
    (writeSuccessHashesLoopSpec ((bv_unsigned sp - 16) ↦ₘ? 16 ∗ P)) -∗
  instr_pre 0x15754
    (writeSuccessSuffixHashes15750NonzeroState
      (Z_to_bv 64 (Z.of_nat (S remaining)))
      (writeSuccessSuffixHashes15750NonzeroQ
        sp (Z_to_bv 64 (Z.of_nat (S remaining)))
        (writeSuccessHashesEvents sp (S remaining) tail)
        (writeSuccessSuffixHashesEntryLoopFrame
          sp pointer base total processed remaining bytes tail P)))%I.
Proof.
  iIntros "#Hloop".
  iApply (instr_pre_wand 0x15754 0x15754 true true with "Hloop");
    [done | reflexivity |].
  iIntros "Hstate".
  iEval (rewrite /writeSuccessSuffixHashes15750NonzeroState) in "Hstate".
  iDestruct "Hstate" as "(Hsys & H8 & Hrest)".
  iEval (rewrite /writeSuccessSuffixHashes15750NonzeroQ) in "Hrest".
  iDestruct "Hrest" as
    "(H1 & H2 & H5 & H10 & H11 & Hstack & Hmmio & HtraceQ & HQ)".
  iEval (rewrite /writeSuccessSuffixHashesEntryLoopFrame) in "HQ".
  iDestruct "HQ" as
    "(Hother & H9 & Hbytes & Hscratch & HP & Hinvariant & Hexit & _)".
  iEval (rewrite /writeSuccessHashesLoopSpec).
  iExists sp, pointer, base, total, processed, remaining, bytes, tail.
  iPoseProof (write_success_suffix_hashes_source_words sp
    with "Hother H1 H5 H10 H11") as "HotherFull".
  iFrame "Hsys HotherFull H2 H8 H9 Hbytes Hscratch Hstack Hmmio HP
    Hinvariant Hexit".
  iExact "HtraceQ".
Qed.
