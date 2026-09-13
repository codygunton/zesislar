Require Import ZesuSsz.Automation.All.
From Coq Require Import Lists.List ZArith.ZArith.
Require Import isla.riscv64.riscv64.
From IslaTraces.write_success_blocks Require Import Index.
Require Import ZesuSsz.Contracts.IslarisCode.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessBitvector.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessTransactionsWithdrawalsTailState.

#[local] Hint Extern 7
  (FindInContext (FindInstrKind ?address ?later) FICSyntactic) =>
  let reduced := eval vm_compute in address in
  first [ constr_eq address reduced; fail 1
        | change (FindInContext (FindInstrKind reduced later) FICSyntactic);
          typeclasses eauto ] : typeclass_instances.

Lemma write_success_transactions_withdrawals_tail_offset
    (sp : bv 64) (offset : Z) :
  (0 <= offset <= 1896)%Z ->
  (bv_unsigned sp + 1896 < 0x40000000)%Z ->
  bv_unsigned (sp + Z_to_bv 64 offset)%bv = bv_unsigned sp + offset.
Proof.
  intros Hoff Hupper.
  pose proof (bv_unsigned_in_range 64 sp) as Hrange.
  rewrite bv_add_unsigned bv_unsigned_BV.
  rewrite (bv_wrap_small 64 offset); last first.
  { unfold bv_modulus. cbn. lia. }
  rewrite (bv_wrap_small 64 (bv_unsigned sp + offset)); first reflexivity.
  unfold bv_modulus in Hrange. cbn in Hrange.
  change (0 <= bv_unsigned sp + offset < 18446744073709551616)%Z. lia.
Qed.

Lemma write_success_transactions_withdrawals_tail_loads
    `{!islaG Sigma} `{!threadG} (P : iProp Sigma) :
  instr_lookup_resources IslaTraces.write_success_blocks.Index.lookup -∗
  instr_pre 0x15680 (writeSuccessTransactionsWithdrawalsAt15680Spec P) -∗
  instr_body 0x15678 (writeSuccessTransactionsWithdrawalsAt15678Spec P).
Proof.
  iStartProof. iIntros "#Hlookup Hnext".
  iPoseProof "Hlookup" as "#Hlookup15678".
  iEval (rewrite /instr_lookup_resources) in "Hlookup15678".
  iPoseProof ("Hlookup15678" $! 0x15678 with "[]") as "#Hinstr15678".
  { iPureIntro. rewrite IslaTraces.write_success_blocks.Index.lookup_a15678. done. }
  iEval (rewrite IslaTraces.write_success_blocks.Index.lookup_a15678)
    in "Hinstr15678".
  iPoseProof "Hlookup" as "#Hlookup1567c".
  iEval (rewrite /instr_lookup_resources) in "Hlookup1567c".
  iPoseProof ("Hlookup1567c" $! 0x1567c with "[]") as "#Hinstr1567c".
  { iPureIntro. rewrite IslaTraces.write_success_blocks.Index.lookup_a1567c. done. }
  iEval (rewrite IslaTraces.write_success_blocks.Index.lookup_a1567c)
    in "Hinstr1567c".
  iClear "Hlookup Hlookup15678 Hlookup1567c".
  rewrite instr_pre'_eq. iIntros "Hentry".
  iEval (rewrite /writeSuccessTransactionsWithdrawalsAt15678Spec) in "Hentry".
  iDestruct "Hentry" as
    (sp pointer base total processed remaining bytes prefix suffix tail)
    "(Hsys & H2 & H8 & H9 & Hframe)".
  iEval (rewrite /writeSuccessTransactionsWithdrawalsTailFrame) in "Hframe".
  iDestruct "Hframe" as
    "(Hpreserved & H1 & H5 & H10 & H11 & H18 & HcallScratch & HpointerWord &
      HcountWord & Hmmio & Htrace & %Halign & %Hlower & %Hupper & Hresources & _)".
  iEval (rewrite reg_mapsto_pred_eq /reg_mapsto_pred_def) in "H8".
  iDestruct "H8" as (r8) "(H8 & _)".
  iEval (rewrite reg_mapsto_pred_eq /reg_mapsto_pred_def) in "H9".
  iDestruct "H9" as (r9) "(H9 & _)".
  have Haddr1120 :=
    write_success_transactions_withdrawals_tail_offset sp 1120 ltac:(lia) Hupper.
  have Haddr1128 :=
    write_success_transactions_withdrawals_tail_offset sp 1128 ltac:(lia) Hupper.
  iEval (rewrite -instr_pre'_eq) in "Hnext".
  replace (bv_wrap 64 87672) with 87672 by bv_solve.
  liARun.
  Unshelve. all: zesu_finish.
  Unshelve.
  zesu_pack (tail, suffix, prefix, bytes, processed, total, base, tt)ₗ.
  all: zesu_run.
  Unshelve. all: zesu_finish.
Qed.
Print Assumptions write_success_transactions_withdrawals_tail_loads.
