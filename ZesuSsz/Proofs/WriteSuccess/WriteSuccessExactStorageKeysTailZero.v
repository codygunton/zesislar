Require Import ZesuSsz.Automation.All.
Require Import isla.riscv64.riscv64.
From ZesuSsz.Proofs.WriteSuccess Require Import
  WriteSuccessExactStorageKeysLoopReturn WriteSuccessExactStorageKeysCounter
  WriteSuccessExactStorageKeysCountBound WriteSuccessExactStorageKeysModel
  WriteSuccessStorageKeysSpec WriteSuccessLoopCommon WriteSuccessExactStorageKeysTail.

Lemma storage_keys_tail_zero `{!islaG Sigma} `{!threadG}
    (x19 sp pointer : bv 64) base total processed remaining bytes tail (P : iProp Sigma) :
  (storageKeysTailState (pointer + BV 64 32)%bv
    (Z_to_bv 64 (Z.of_nat (S remaining)) - BV 64 1)%bv
    (storageKeysTailFrame x19 sp pointer base total processed remaining bytes tail P) ∗
   ⌜(Z_to_bv 64 (Z.of_nat (S remaining)) - BV 64 1)%bv = BV 64 0⌝ ∗ True) -∗
  (writeSuccessStorageKeysLoopExit x19 sp base total bytes tail P ∗
   instr_pre 0x153b4 (writeSuccessStorageKeysLoopExit x19 sp base total bytes tail P) ∗ True).
Proof.
  rewrite storage_keys_counter_decrement.
  iIntros "(Hstate & %Hzero & _)".
  iEval (unfold storageKeysTailState, storageKeysTailFrame,
    writeSuccessFixedWidthArrayInvariant) in "Hstate".
  iDestruct "Hstate" as
    "(Hsys & Hpointer & Hcount & (Hregs & H19 & Hsp & Harray & Hscratch & Hmmio & Htrace & HP & (%Htotal & %Hlength & %Hposition & %Hbound & %Halign & %Hsplow & %Hsphigh & %Hbaselow & %Hbasehigh & _) & Hexit & _) & _)".
  have Hremaining : remaining = 0%nat :=
    storage_keys_counter_zero remaining (storage_keys_count_bound remaining Hbound) Hzero.
  subst remaining. clear Hbound.
  have Hadvance : bv_unsigned (pointer + BV 64 32)%bv = base + 32 * Z.of_nat (S processed).
  { apply storage_keys_pointer_advance; [lia|lia|exact Hposition]. }
  iEval (rewrite writeSuccessExactStorageKeysEvents_zero) in "Htrace".
  iSplitL "Hsys Hpointer Hcount Hregs H19 Hsp Harray Hscratch Hmmio Htrace HP".
  2: { iFrame. }
  iEval (unfold writeSuccessStorageKeysLoopExit).
  iExists (pointer + BV 64 32)%bv.
  iEval (rewrite Hzero) in "Hcount".
  iFrame. repeat iSplit; try (iPureIntro; lia); done.
Qed.
Print Assumptions storage_keys_tail_zero.
