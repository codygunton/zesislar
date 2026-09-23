Require Import ZesuSsz.Automation.All.
From Coq Require Import Lia Lists.List ZArith.ZArith.
Require Import ZesuSsz.Compliance.BugPredicates.
Require Import ZesuSsz.Compliance.BugWitnessReads.

Lemma transactionCountWitnessLayout :
  exists layout,
    zesuBugLayout transactionCountWitnessInput = Some layout /\
    bugTransactionCount layout = Some 1048577.
Proof.
  unfold zesuBugLayout.
  rewrite tx_payload.
  rewrite tx_read_2, tx_read_6, tx_read_10, tx_read_14.
  rewrite tx_read_18, tx_read_22, tx_read_58.
  rewrite tx_read_chain_expr, tx_read_chain_offset_expr.
  replace (2 + Z.to_nat 16 + Z.to_nat 4194924)%nat with 4194942%nat
    by (apply Nat.eqb_eq; vm_compute; reflexivity).
  rewrite tx_read_request.
  rewrite tx_read_498, tx_read_566, tx_read_466, tx_read_490.
  replace (2 + Z.to_nat 4194972 + Z.to_nat 12)%nat with 4194986%nat
    by (apply Nat.eqb_eq; vm_compute; reflexivity).
  rewrite tx_read_active_offset.
  replace (4194986 + Z.to_nat 4)%nat with 4194990%nat
    by (apply Nat.eqb_eq; vm_compute; reflexivity).
  rewrite tx_read_block_offset.
  replace (4194990 + 4)%nat with 4194994%nat
    by (apply Nat.eqb_eq; vm_compute; reflexivity).
  rewrite tx_read_timestamp_offset.
  replace (4194990 + Z.to_nat 8)%nat with 4194998%nat
    by (apply Nat.eqb_eq; vm_compute; reflexivity).
  replace (4194990 + Z.to_nat 16)%nat with 4195006%nat
    by (apply Nat.eqb_eq; vm_compute; reflexivity).
  unfold zesuReadOptionalU64.
  rewrite tx_read_block_activation, tx_read_timestamp_activation.
  replace (8 <=? Z.to_nat 16 - Z.to_nat 8)%nat with true
    by (vm_compute; reflexivity).
  replace (8 <=? 2 + Z.to_nat 4195012 - 4195006)%nat with true
    by (vm_compute; reflexivity).
  eexists; split; [reflexivity|].
  cbn [bugTransactionCount].
  rewrite tx_read_570.
  replace (2 + Z.to_nat 16 + Z.to_nat 44 + Z.to_nat 540)%nat
    with 602%nat by reflexivity.
  replace (Z.to_nat 4194848 - Z.to_nat 540)%nat with 4194308%nat
    by (apply Nat.eqb_eq; vm_compute; reflexivity).
  rewrite transactionCountWitnessInputCount.
  reflexivity.
Qed.

Print Assumptions transactionCountWitnessLayout.
