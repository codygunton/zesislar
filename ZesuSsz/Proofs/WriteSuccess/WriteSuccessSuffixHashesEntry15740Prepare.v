From Coq Require Import ZArith.ZArith.
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessLoopCommon.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessSuffixHashesEntryCallerResources.

Local Instance writeSuccessFixedWidthArrayInvariant_persistent
    `{!islaG Sigma} `{!threadG}
    (sp pointer : bv 64) (base : Z)
    (total processed remaining : nat) (bytes : list (bv 8)) :
    Persistent (writeSuccessFixedWidthArrayInvariant
      sp pointer base total processed remaining bytes).
Proof. rewrite /writeSuccessFixedWidthArrayInvariant. apply _. Qed.

Lemma write_success_suffix_hashes_15740_prepare
    `{!islaG Sigma} `{!threadG} (P : iProp Sigma) :
  writeSuccessSuffixHashesAt15740Spec P -∗
  ∃ (sp pointer : bv 64) (base : Z)
      (total processed remaining : nat) (bytes : list (bv 8))
      (tail : spec),
    writeSuccessSuffixHashes15740State P sp pointer base total processed
      remaining bytes tail.
Proof.
  iIntros "Hentry".
  rewrite /writeSuccessSuffixHashesAt15740Spec.
  iDestruct "Hentry" as
    (sp pointer base total processed remaining bytes tail)
    "(Hsys & Hregs & H2 & H8 & H9 & Hbytes & Hscratch & H904 & H912 &
      Hstack & Hmmio & Htrace & HP & Hinvariant & Hnext & _)".
  iDestruct (persistent with "Hinvariant") as "#Hinvariant".
  iPoseProof "Hinvariant" as "HinvCopy".
  iEval (rewrite /writeSuccessFixedWidthArrayInvariant) in "HinvCopy".
  iDestruct "HinvCopy" as
    "(%Htotal & %HbytesLength & %Hpointer & %HremainingBound & %HspAlign &
      %HspMin & %HspMax & %HbaseMin & %HbaseMax & _)".
  have H912Address :
      bv_unsigned (sp + BV 64 912)%bv = bv_unsigned sp + 912.
  { rewrite bv_add_unsigned bv_unsigned_BV.
    apply bv_wrap_small.
    pose proof (bv_unsigned_in_range 64 sp).
    unfold bv_modulus in *; cbn in *; lia. }
  have H912Align :
      bv_extract 0 3 (sp + BV 64 912)%bv = BV 3 0.
  { clear - HspAlign. bv_simplify_arith HspAlign; bv_solve. }
  have H912RamLower :
      bv_unsigned (sp + BV 64 912)%bv >= bv_unsigned (BV 64 0x20000000) by
    apply write_success_suffix_ram_lower_912; assumption.
  have H912RamUpper :
      bv_unsigned (sp + BV 64 912)%bv <=
        bv_unsigned (BV 64 0x20000000 + BV 64 0x20000000 - BV 64 8)%bv by
    apply write_success_suffix_ram_upper_912; assumption.
  iExists sp, pointer, base, total, processed, remaining, bytes, tail.
  rewrite /writeSuccessSuffixHashes15740State.
  iAssert ("x8" ↦ᵣ: (fun _ => True))%I with "[H8]" as "H8Any".
  { rewrite reg_mapsto_pred_eq /reg_mapsto_pred_def.
    iExists _. iFrame. }
  iEval (rewrite <- H912Address) in "H912".
  iFrame "Hsys H8Any H2 H912".
  iSplit; first (iPureIntro; exact H912Align).
  iSplit; first (iPureIntro; exact H912RamLower).
  iSplit; first (iPureIntro; exact H912RamUpper).
  rewrite /writeSuccessSuffixHashes15740Frame.
  iFrame "Hregs H9 Hbytes Hscratch H904 Hstack Hmmio Htrace HP Hinvariant Hnext".
Qed.
