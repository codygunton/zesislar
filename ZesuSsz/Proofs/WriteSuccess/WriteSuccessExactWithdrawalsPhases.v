Require Import ZesuSsz.Automation.All.
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Export.Snapshots.
From Coq Require Import Lists.List ZArith.ZArith.
From ZesuSsz.Proofs.WriteSuccess Require Import
  WriteSuccessExactAuthorizationsPayloads WriteSuccessPrivatePublicBytes
  WriteSuccessRepresentation WriteSuccessEncodeFragments WriteSuccessOutputSemantic
  WriteSuccessOutputDescriptors WriteSuccessObservation WriteSuccessExactTransactionsGasLoads.

Definition withdrawalExactPhaseEvents (phase : nat) (sp : bv 64)
    (bytes : list (bv 8)) (tail : spec) : spec :=
  writeOutputPayloadsSpec (drop phase (writeSuccessWithdrawalsItemDescriptors sp 1))
    (drop phase (map writeSuccessPrivateBytes (writeSuccessWithdrawalFragments
      (writeSuccessWithdrawalObservationOfBytes bytes)))) tail.

Lemma withdrawal_phase_0 sp bytes tail :
  length bytes = 48%nat ->
  withdrawalExactPhaseEvents 0 sp bytes tail =
  writeOutputEvents (sp - BV 64 16)%bv (BV 64 8)
    (writeSuccessPrivateBytes (writeSuccessEncodeU64
      (bv_unsigned (transactionRowWord bytes 0 0))))
    (withdrawalExactPhaseEvents 1 sp bytes tail).
Proof. intros Hlen. rewrite authorization_int_payload; [reflexivity|lia]. Qed.
Print Assumptions withdrawal_phase_0.

Lemma withdrawal_phase_1 sp bytes tail :
  length bytes = 48%nat ->
  withdrawalExactPhaseEvents 1 sp bytes tail =
  writeOutputEvents (sp - BV 64 16)%bv (BV 64 8)
    (writeSuccessPrivateBytes (writeSuccessEncodeU64
      (bv_unsigned (transactionRowWord bytes 0 8))))
    (withdrawalExactPhaseEvents 2 sp bytes tail).
Proof. intros Hlen. rewrite authorization_int_payload; [reflexivity|lia]. Qed.
Print Assumptions withdrawal_phase_1.

Lemma withdrawal_phase_3 sp bytes tail :
  length bytes = 48%nat ->
  withdrawalExactPhaseEvents 3 sp bytes tail =
  writeOutputEvents (sp - BV 64 16)%bv (BV 64 8)
    (writeSuccessPrivateBytes (writeSuccessEncodeU64
      (bv_unsigned (transactionRowWord bytes 0 16))))
    (withdrawalExactPhaseEvents 4 sp bytes tail).
Proof. intros Hlen. rewrite authorization_int_payload; [reflexivity|lia]. Qed.
Print Assumptions withdrawal_phase_3.

Lemma withdrawal_phase_2 sp bytes tail :
  withdrawalExactPhaseEvents 2 sp bytes tail =
  writeOutputEvents (sp + BV 64 1768)%bv (BV 64 20)
    (take 20 (drop 24 bytes)) (withdrawalExactPhaseEvents 3 sp bytes tail).
Proof.
  change (writeOutputEvents (sp + BV 64 1768)%bv (BV 64 20)
    (writeSuccessPrivateBytes (writeSuccessPublicBytes (take 20 (drop 24 bytes))))
    (withdrawalExactPhaseEvents 3 sp bytes tail) =
    writeOutputEvents (sp + BV 64 1768)%bv (BV 64 20)
      (take 20 (drop 24 bytes)) (withdrawalExactPhaseEvents 3 sp bytes tail)).
  rewrite writeSuccessPrivatePublicBytes. reflexivity.
Qed.
Print Assumptions withdrawal_phase_2.

Lemma withdrawal_phase_4 sp bytes tail : withdrawalExactPhaseEvents 4 sp bytes tail = tail.
Proof. reflexivity. Qed.
Print Assumptions withdrawal_phase_4.
