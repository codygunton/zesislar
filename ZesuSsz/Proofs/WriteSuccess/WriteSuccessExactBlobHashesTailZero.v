Require Import ZesuSsz.Automation.AllLegacy.
Require Import isla.riscv64.riscv64.
From ZesuSsz.Proofs.WriteSuccess Require Import
  WriteSuccessExactBlobHashesLoopReturn WriteSuccessExactBlobHashesTailRegisters
  WriteSuccessExactStorageKeysCounter WriteSuccessExactStorageKeysCountBound
  WriteSuccessExactBlobHashesModel WriteSuccessBlobHashesSpec WriteSuccessLoopCommon
  WriteSuccessExactBlobHashesTail.

Lemma blob_tail_zero `{!islaG Sigma} `{!threadG}
    (sp pointer : bv 64) base total processed remaining bytes tail (P : iProp Sigma) :
  (blobTailState (pointer + BV 64 32)%bv (Z_to_bv 64 (Z.of_nat (S remaining))) (Z_to_bv 64 (Z.of_nat (S remaining)) - BV 64 1)%bv
    (blobTailFrame sp pointer base total processed remaining bytes tail P) ∗
   ⌜(Z_to_bv 64 (Z.of_nat (S remaining)) - BV 64 1)%bv = BV 64 0⌝ ∗ True)%I -∗
  (writeSuccessBlobHashesLoopExit sp base total bytes tail P ∗
   instr_pre 0x15564 (writeSuccessBlobHashesLoopExit sp base total bytes tail P) ∗ True)%I.
Proof.
  rewrite storage_keys_counter_decrement.
  iIntros "(Hstate & %Hzero & _)".
  iEval (unfold blobTailState, blobTailFrame, writeSuccessFixedWidthArrayInvariant) in "Hstate".
  iDestruct "Hstate" as
    "(Hsys & Hpointer & Hsaved & Hcountreg &
      (Hregs & Hsp & Harray & Hscratch & Hmmio & Htrace & HP &
        (%Htotal & %Hlength & %Hposition & %Hbound & %Halign & %Hsplow & %Hsphigh & %Hbaselow & %Hbasehigh & _) & Hexit & _) & _)".
  iPoseProof (blob_tail_registers with "[Hregs Hsaved]") as "Hother". { iFrame. }
  have Hremaining : remaining = 0%nat :=
    storage_keys_counter_zero remaining (storage_keys_count_bound remaining Hbound) Hzero.
  subst remaining. clear Hbound.
  have Hadvance : bv_unsigned (pointer + BV 64 32)%bv = base + 32 * Z.of_nat (S processed).
  { apply storage_keys_pointer_advance; [lia|lia|exact Hposition]. }
  iEval (rewrite writeSuccessExactBlobHashesEvents_zero) in "Htrace".
  iSplitL "Hsys Hpointer Hcountreg Hother Hsp Harray Hscratch Hmmio Htrace HP".
  2: { iFrame. }
  iEval (unfold writeSuccessBlobHashesLoopExit).
  iExists (pointer + BV 64 32)%bv.
  iEval (rewrite Hzero) in "Hcountreg".
  iFrame. repeat iSplit; try (iPureIntro; lia); done.
Qed.
Print Assumptions blob_tail_zero.
