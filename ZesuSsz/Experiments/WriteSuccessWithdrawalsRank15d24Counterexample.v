From Coq Require Import Lists.List ZArith.ZArith.
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Experiments.WriteSuccessSegment15694.
Require Import ZesuSsz.Experiments.WriteSuccessSegment15d24.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsOperational.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsOperationalData.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsRank.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsRankGeneral.
Require Import ZesuSsz.Experiments.WriteSuccessWithdrawalsRankIndexed.

Open Scope Z_scope.

Lemma writeSuccess15d24LinkExact :
  writeSuccess15d24Link = Z_to_bv 64 0xfd24.
Proof. vm_compute. apply bv_eq. reflexivity. Qed.

Definition writeSuccessWithdrawalsOld15d28Occurrence
    (state : WriteSuccessWithdrawalsConcreteState) : option nat :=
  address ← writeSuccessWithdrawalsRegisterUnsigned state "x1";
  Some (writeSuccessWithdrawalsIntegerOccurrence address).

Lemma writeSuccessWithdrawals15d28OldOccurrenceAfter15d24 regs global log :
  writeSuccessWithdrawalsOld15d28Occurrence
    (writeSuccess15d24After regs global, log) = Some 3%nat.
Proof.
  unfold writeSuccessWithdrawalsOld15d28Occurrence,
    writeSuccessWithdrawalsRegisterUnsigned, writeSuccess15d24After,
    writeSuccess15694Local, writeSuccess15d24Regs. cbn.
  rewrite lookup_insert_ne; last discriminate. rewrite lookup_insert.
  rewrite writeSuccess15d24LinkExact. vm_compute. reflexivity.
Qed.

Lemma writeSuccessWithdrawals15d28CheckedOccurrence :
  count_occ Z.eq_dec
    (firstn (342 + 11) writeSuccessWithdrawalsIterationPcs) 0x15d28 = 0%nat.
Proof. reflexivity. Qed.

Theorem writeSuccessWithdrawals15d24SuccessorOccurrenceConflict regs global log :
  writeSuccessWithdrawalsOld15d28Occurrence
    (writeSuccess15d24After regs global, log) <>
  Some (count_occ Z.eq_dec
    (firstn (342 + 11) writeSuccessWithdrawalsIterationPcs) 0x15d28).
Proof.
  rewrite writeSuccessWithdrawals15d28OldOccurrenceAfter15d24
    writeSuccessWithdrawals15d28CheckedOccurrence. discriminate.
Qed.

Print Assumptions writeSuccess15d24LinkExact.
Print Assumptions writeSuccessWithdrawals15d28OldOccurrenceAfter15d24.
Print Assumptions writeSuccessWithdrawals15d28CheckedOccurrence.
Print Assumptions writeSuccessWithdrawals15d24SuccessorOccurrenceConflict.
