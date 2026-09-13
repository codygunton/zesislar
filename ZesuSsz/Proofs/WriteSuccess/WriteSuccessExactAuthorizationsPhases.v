Require Import ZesuSsz.Automation.All.
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Export.Snapshots.
From Coq Require Import Lists.List ZArith.ZArith.
From ZesuSsz.Proofs.WriteSuccess Require Import
  WriteSuccessExactAuthorizationsModel WriteSuccessExactAuthorizationsPayloads
  WriteSuccessPrivatePublicBytes WriteSuccessRepresentation WriteSuccessEncodeFragments
  WriteSuccessOutputSemantic WriteSuccessOutputDescriptors WriteSuccessObservation
  WriteSuccessExactEncoderU256Spec WriteSuccessExactTransactionsGasLoads.

Definition authorizationExactPhaseEvents (phase : nat) (sp : bv 64)
    (bytes : list (bv 8)) (tail : spec) : spec :=
  writeOutputPayloadsSpec (drop phase (writeSuccessAuthorizationsDescriptors sp 1))
    (drop phase (map writeSuccessPrivateBytes (writeSuccessAuthorizationFragments
      (writeSuccessAuthorizationObservationOfBytes bytes)))) tail.

Lemma authorization_phase_zero sp bytes tail :
  length bytes = 144%nat ->
  authorizationExactPhaseEvents 0 sp bytes tail =
  writeOutputEvents (sp - BV 64 48)%bv (BV 64 32)
    (writeSuccessU256WordsPayload (transactionRowWord bytes 0 0)
      (transactionRowWord bytes 0 8) (transactionRowWord bytes 0 16)
      (transactionRowWord bytes 0 24)) (authorizationExactPhaseEvents 1 sp bytes tail).
Proof.
  intros Hlen. rewrite authorization_u256_payload; [|lia].
  reflexivity.
Qed.
Print Assumptions authorization_phase_zero.

Lemma authorization_phase_one sp bytes tail :
  authorizationExactPhaseEvents 1 sp bytes tail =
  writeOutputEvents (sp + BV 64 1856)%bv (BV 64 20)
    (take 20 (drop 112 bytes)) (authorizationExactPhaseEvents 2 sp bytes tail).
Proof.
  change (writeOutputEvents (sp + BV 64 1856)%bv (BV 64 20)
    (writeSuccessPrivateBytes (writeSuccessPublicBytes (take 20 (drop 112 bytes))))
    (authorizationExactPhaseEvents 2 sp bytes tail) =
    writeOutputEvents (sp + BV 64 1856)%bv (BV 64 20)
      (take 20 (drop 112 bytes)) (authorizationExactPhaseEvents 2 sp bytes tail)).
  rewrite writeSuccessPrivatePublicBytes. reflexivity.
Qed.
Print Assumptions authorization_phase_one.

Lemma authorization_phase_two sp bytes tail :
  length bytes = 144%nat ->
  authorizationExactPhaseEvents 2 sp bytes tail =
  writeOutputEvents (sp - BV 64 16)%bv (BV 64 8)
    (writeSuccessPrivateBytes (writeSuccessEncodeU64
      (bv_unsigned (transactionRowWord bytes 0 96))))
    (authorizationExactPhaseEvents 3 sp bytes tail).
Proof. intros Hlen. rewrite authorization_int_payload; [reflexivity|lia]. Qed.
Print Assumptions authorization_phase_two.

Lemma authorization_phase_three sp bytes tail :
  length bytes = 144%nat ->
  authorizationExactPhaseEvents 3 sp bytes tail =
  writeOutputEvents (sp - BV 64 16)%bv (BV 64 8)
    (writeSuccessPrivateBytes (writeSuccessEncodeU64
      (bv_unsigned (transactionRowWord bytes 0 104))))
    (authorizationExactPhaseEvents 4 sp bytes tail).
Proof. intros Hlen. rewrite authorization_int_payload; [reflexivity|lia]. Qed.
Print Assumptions authorization_phase_three.

Lemma authorization_phase_four sp bytes tail :
  length bytes = 144%nat ->
  authorizationExactPhaseEvents 4 sp bytes tail =
  writeOutputEvents (sp - BV 64 48)%bv (BV 64 32)
    (writeSuccessU256WordsPayload (transactionRowWord bytes 32 0)
      (transactionRowWord bytes 32 8) (transactionRowWord bytes 32 16)
      (transactionRowWord bytes 32 24))
    (authorizationExactPhaseEvents 5 sp bytes tail).
Proof. intros Hlen. rewrite authorization_u256_payload; [reflexivity|lia]. Qed.
Print Assumptions authorization_phase_four.

Lemma authorization_phase_five sp bytes tail :
  length bytes = 144%nat ->
  authorizationExactPhaseEvents 5 sp bytes tail =
  writeOutputEvents (sp - BV 64 48)%bv (BV 64 32)
    (writeSuccessU256WordsPayload (transactionRowWord bytes 64 0)
      (transactionRowWord bytes 64 8) (transactionRowWord bytes 64 16)
      (transactionRowWord bytes 64 24))
    (authorizationExactPhaseEvents 6 sp bytes tail).
Proof. intros Hlen. rewrite authorization_u256_payload; [reflexivity|lia]. Qed.
Print Assumptions authorization_phase_five.

Lemma authorization_phase_six sp bytes tail :
  authorizationExactPhaseEvents 6 sp bytes tail = tail.
Proof. reflexivity. Qed.
Print Assumptions authorization_phase_six.

Lemma authorization_phase_item sp bytes tail :
  authorizationExactPhaseEvents 0 sp bytes tail =
  writeSuccessExactAuthorizationItemEvents sp bytes tail.
Proof. reflexivity. Qed.
Print Assumptions authorization_phase_item.
