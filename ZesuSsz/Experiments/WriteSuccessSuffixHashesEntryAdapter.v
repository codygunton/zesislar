From Coq Require Import Lists.List ZArith.ZArith.
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Experiments.WriteSuccessHashesLoop.
Require Import ZesuSsz.Experiments.WriteSuccessEncoderIntCall.
Require Import ZesuSsz.Experiments.WriteSuccessSuffixHashesContinuationAdapters.
Require Import ZesuSsz.Experiments.WriteSuccessSuffixHashes15750Branch.
Require Import ZesuSsz.Experiments.WriteSuccessSuffixHashesCallContinuations.
Require Import ZesuSsz.Experiments.WriteSuccessSuffixHashes1574cNonzeroCaller.
Require Import ZesuSsz.Experiments.WriteSuccessSuffixHashes15748Compose.
Require Import ZesuSsz.Experiments.WriteSuccessSuffixHashes15744Compose.
Require Import ZesuSsz.Experiments.WriteSuccessSuffixHashesQContinuations.

Lemma write_success_suffix_hashes_entry_count_nonzero
    (remaining : nat) (HremainingBound : (S remaining < 2 ^ 64)%nat) :
  Z_to_bv 64 (Z.of_nat (S remaining)) <> BV 64 0.
Proof.
  intro Hzero.
  have HzeroUnsigned := f_equal bv_unsigned Hzero.
  rewrite Z_to_bv_unsigned in HzeroUnsigned.
  have HboundZ :=
    (proj1 (Nat2Z.inj_lt (S remaining) (2 ^ 64))) HremainingBound.
  rewrite Nat2Z.inj_pow in HboundZ.
  have Hrange :
      0 <= Z.of_nat (S remaining) < bv_modulus 64.
  { unfold bv_modulus. cbn. lia. }
  rewrite (bv_wrap_small 64 _ Hrange) in HzeroUnsigned.
  rewrite bv_unsigned_BV in HzeroUnsigned.
  cbn in HzeroUnsigned. lia.
Qed.

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
  □ instr_pre 0x15754 (writeSuccessHashesLoopSpec P) -∗
  instr_body 0x15744
    (writeSuccessSuffixHashes15744NonzeroSpec sp
      (Z_to_bv 64 (Z.of_nat (S remaining))) tail
      (writeSuccessSuffixHashesLoopResources
        sp pointer base total processed remaining bytes tail P)).
Proof.
  iIntros "H44 H48 H4c #Hint H50 #Hloop".
  have Hvalue :
      Z_to_bv 64 (Z.of_nat (S remaining)) <> BV 64 0.
  { apply write_success_suffix_hashes_entry_count_nonzero.
    exact HremainingBound. }
  iAssert (instr_pre 0x15754
      (writeSuccessSuffixHashes15750NonzeroState
        (Z_to_bv 64 (Z.of_nat (S remaining)))
        (writeSuccessSuffixHashes15750NonzeroQ
          sp (Z_to_bv 64 (Z.of_nat (S remaining))) tail
          (writeSuccessSuffixHashesLoopResources
            sp pointer base total processed remaining bytes tail P))))%I
    with "[Hloop]" as "HbranchPre".
  { iApply (instr_pre_wand 0x15754 0x15754 true true with "Hloop");
      [done | reflexivity |].
    iIntros "Hstate".
    iEval (rewrite /writeSuccessSuffixHashes15750NonzeroState) in "Hstate".
    iDestruct "Hstate" as "(Hsys & H8 & Hrest)".
    iEval (rewrite /writeSuccessSuffixHashes15750NonzeroQ) in "Hrest".
    iDestruct "Hrest" as
      "(H1 & H2 & H5 & H10 & H11 & Hstack & Hmmio & Htrace & HQ)".
    iEval (rewrite /writeSuccessSuffixHashesLoopResources) in "HQ".
    iDestruct "HQ" as
      "(Hother & H2loop & H9 & Hbytes & Hscratch & HmmioLoop &
        HtraceLoop & HP & Hinvariant & Hexit & _)".
    iEval (rewrite /writeSuccessHashesLoopSpec).
    iExists sp, pointer, base, total, processed, remaining, bytes, tail.
    iFrame "Hsys Hother H2 H8 H9 Hbytes Hscratch Hmmio HtraceLoop HP
      Hinvariant Hexit".
  }
  iPoseProof (write_success_suffix_hashes_15750_nonzero_state
    (Z_to_bv 64 (Z.of_nat (S remaining)))
    (writeSuccessSuffixHashes15750NonzeroQ
      sp (Z_to_bv 64 (Z.of_nat (S remaining))) tail
      (writeSuccessSuffixHashesLoopResources
        sp pointer base total processed remaining bytes tail P)) Hvalue
    with "H50 HbranchPre") as "Hbranch".
  iPoseProof (write_success_suffix_hashes_1574c_nonzero_caller
    sp (Z_to_bv 64 (Z.of_nat (S remaining))) tail
    (writeSuccessSuffixHashesLoopResources
      sp pointer base total processed remaining bytes tail P) Hvalue
    with "H4c Hint Hbranch") as "H4cBody".
  iPoseProof (write_success_suffix_hashes_15748_nonzero_compose
    sp (Z_to_bv 64 (Z.of_nat (S remaining))) tail
    (writeSuccessSuffixHashesLoopResources
      sp pointer base total processed remaining bytes tail P)
    with "H48 H4cBody") as "H48Body".
  iApply (write_success_suffix_hashes_15744_nonzero_compose
    sp (Z_to_bv 64 (Z.of_nat (S remaining))) tail
    (writeSuccessSuffixHashesLoopResources
      sp pointer base total processed remaining bytes tail P)
    with "H44 H48Body").
Qed.
