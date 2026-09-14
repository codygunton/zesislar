Require Import ZesuSsz.Automation.All.
Require Import ZesuMachineMap.Machine.
From Coq Require Import Lists.List ZArith.ZArith.
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessTransactionsSpec.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessTransactionsBoundary1519c.

Lemma write_success_transactions_chunk_1519c_adapter
    `{!islaG Sigma} `{!threadG} (P : iProp Sigma)
    (sp : bv 64) (base : Z) (transaction : writeSuccessTransaction)
    (transactions processed remaining : list writeSuccessTransaction)
    (bytes prefix suffix : list (bv 8)) (tail : spec) :
  bv_unsigned sp `mod` 16 = 0 ->
  (mapRamBase defaultMap) <= bv_unsigned sp - 48 ->
  bv_unsigned sp + 1896 < (machineRamEnd defaultMap) ->
  writeSuccessTransactionPhaseHandoff TransactionValue
    (writeSuccessTransactionsMachine151a0
      sp base transactions processed transaction)
    sp base transaction transactions processed remaining
    bytes prefix suffix tail P -∗
  ∃ x : spec *ₗ
      list (bv 8) *ₗ list (bv 8) *ₗ list (bv 8) *ₗ
      list writeSuccessTransaction *ₗ list writeSuccessTransaction *ₗ
      list writeSuccessTransaction *ₗ writeSuccessTransaction *ₗ
      Z *ₗ bv 64 *ₗ (),
    ⌜bv_extract 0 3 (x.nextₗ.9ₗ + 128) = 0%bv⌝ ∗
    ⌜(mapRamBase defaultMap) <= bv_unsigned (x.nextₗ.9ₗ + 128)⌝ ∗
    ⌜bv_unsigned (x.nextₗ.9ₗ + 128) <= machineRamEnd defaultMap - 8⌝ ∗
    writeSuccessTransactionPhaseHandoff TransactionValue
      (writeSuccessTransactionsMachine151a0
        x.nextₗ.9ₗ x.9ₗ x.7ₗ x.6ₗ x.8ₗ)
      x.nextₗ.9ₗ x.9ₗ x.8ₗ x.7ₗ x.6ₗ x.5ₗ
      x.4ₗ x.3ₗ x.2ₗ x.1ₗ P.
Proof.
  intros Halign Hmin Hmax.
  iStartProof.
  iIntros "Hphase".
  have Hsp128 : bv_unsigned (sp + 128) = bv_unsigned sp + 128 by
    (rewrite bv_add_unsigned bv_unsigned_BV;
     apply bv_wrap_small;
     pose proof (bv_unsigned_in_range 64 sp);
     pose proof (bv_unsigned_in_range 64 (BV 64 128));
     unfold bv_modulus in *; cbn in *; lia).
  have Hextract128 : bv_extract 0 3 (sp + 128) = 0%bv by bv_solve.
  iExists (tail, suffix, prefix, bytes, remaining, processed, transactions,
    transaction, base, sp, tt)ₗ.
  iSplit; first (iPureIntro; exact Hextract128).
  iSplit; first (iPureIntro; rewrite Hsp128; lia).
  iSplit; first (iPureIntro; rewrite Hsp128; lia).
  iFrame.
Qed.
