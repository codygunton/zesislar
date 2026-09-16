Require Import ZesuSsz.Automation.AllLegacy.
Require Import isla.riscv64.riscv64.
From ZesuSsz.Proofs.WriteSuccess Require Import
  WriteSuccessExactStorageKeysLoopReturn WriteSuccessExactStorageKeysCounter
  WriteSuccessExactStorageKeysSpec WriteSuccessLoopCommon WriteSuccessExactStorageKeysTail.

Lemma storage_keys_tail_positive `{!islaG Sigma} `{!threadG}
    (x19 sp pointer : bv 64) base total processed remaining bytes tail (P : iProp Sigma) :
  (storageKeysTailState (pointer + BV 64 32)%bv
    (Z_to_bv 64 (Z.of_nat (S remaining)) - BV 64 1)%bv
    (storageKeysTailFrame x19 sp pointer base total processed remaining bytes tail P) ∗
   ⌜(Z_to_bv 64 (Z.of_nat (S remaining)) - BV 64 1)%bv <> BV 64 0⌝ ∗ True) -∗
  writeSuccessExactStorageKeysLoopSpec x19 P.
Proof.
  rewrite storage_keys_counter_decrement.
  iIntros "(Hstate & %Hnonzero & _)".
  destruct remaining as [|remaining]; [exfalso; apply Hnonzero; apply bv_eq; reflexivity|].
  iEval (unfold storageKeysTailState, storageKeysTailFrame,
    writeSuccessFixedWidthArrayInvariant) in "Hstate".
  iDestruct "Hstate" as
    "(Hsys & Hpointer & Hcount & (Hregs & H19 & Hsp & Harray & Hscratch & Hmmio & Htrace & HP & (%Htotal & %Hlength & %Hposition & %Hbound & %Halign & %Hsplow & %Hsphigh & %Hbaselow & %Hbasehigh & _) & Hexit & _) & _)".
  have Hadvance : bv_unsigned (pointer + BV 64 32)%bv = base + 32 * Z.of_nat (S processed).
  { clear Hbound. apply storage_keys_pointer_advance; [lia|lia|exact Hposition]. }
  have Hnewbound : (S remaining < 2 ^ 64)%nat :=
    Nat.lt_trans _ _ _ (Nat.lt_succ_diag_r _) Hbound.
  iEval (unfold writeSuccessExactStorageKeysLoopSpec).
  iExists sp, (pointer + BV 64 32)%bv, base, total, (S processed), remaining, bytes, tail.
  iFrame. iEval (unfold writeSuccessFixedWidthArrayInvariant).
  repeat iSplit; try (iPureIntro; first [assumption | clear Hbound Hnewbound; lia]); done.
Qed.
Print Assumptions storage_keys_tail_positive.
