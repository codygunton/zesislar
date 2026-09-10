Require Import ZesuSsz.Automation.All.
From Coq Require Import Lists.List ZArith.ZArith.
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Contracts.IslarisMemory.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessTransactionsSpec.

Lemma write_success_transactions_access_array_nonzero
    `{!islaG Sigma} (pointer : bv 64) (bytes : list (bv 8))
    (Hnonempty : bytes <> []) :
  writeSuccessByteArrayOwn pointer bytes -∗
  bv_unsigned pointer ↦ₘ∗ ([] : list (bv 8)) ∗
  bv_unsigned pointer ↦ₘ∗ bytes ∗
  ⌜0x20000000 <= bv_unsigned pointer⌝ ∗
  ⌜bv_unsigned pointer + Z.of_nat (length bytes) < 0x40000000⌝.
Proof.
  destruct bytes as [|byte bytes]; first contradiction.
  iIntros "Haccess".
  iEval (rewrite /writeSuccessByteArrayOwn /=) in "Haccess".
  iDestruct "Haccess" as "(Harray & %Hlow & %Hhigh & _)".
  iDestruct (mem_mapsto_array_app 8%N (bv_unsigned pointer) (DfracOwn 1)
    ([] : list (bv 8)) (byte :: bytes) with "[Harray]")
    as "(Hempty & Harray)"; first (cbn; iExact "Harray").
  iEval (cbn; rewrite Z.add_0_r) in "Harray".
  iFrame "Hempty Harray".
  repeat iSplit; iPureIntro; assumption.
Qed.

Lemma write_success_transactions_access_array_restore_nonzero
    `{!islaG Sigma} (pointer : bv 64) (bytes : list (bv 8))
    (Hnonempty : bytes <> [])
    (Hlow : 0x20000000 <= bv_unsigned pointer)
    (Hhigh : bv_unsigned pointer + Z.of_nat (length bytes) < 0x40000000) :
  bv_unsigned pointer ↦ₘ∗ bytes -∗
  writeSuccessByteArrayOwn pointer bytes.
Proof.
  destruct bytes as [|byte bytes]; first contradiction.
  iIntros "Harray". rewrite /writeSuccessByteArrayOwn /=.
  iFrame "Harray". iPureIntro. repeat split; try assumption; trivial.
Qed.
