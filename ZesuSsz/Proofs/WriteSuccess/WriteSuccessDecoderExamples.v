Require Import ZesuSsz.Automation.All.
From Coq Require Import Lists.List ZArith.ZArith.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessObservation.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessObservationDecoder.

Import ListNotations.
Open Scope Z_scope.

Definition writeSuccessCp1ObservationWithBaseFee
    (baseFee : Z) : WriteSuccessObservation := {|
  observationParentHash := repeat 0 32;
  observationFeeRecipient := repeat 0 20;
  observationStateRoot := repeat 0 32;
  observationReceiptsRoot := repeat 0 32;
  observationLogsBloom := repeat 0 256;
  observationPrevRandao := repeat 0 32;
  observationBlockNumber := 1;
  observationGasLimit := 2;
  observationGasUsed := 3;
  observationTimestamp := 4;
  observationExtraData := [5; 6];
  observationBaseFee := baseFee;
  observationBlockHash := repeat 0 32;
  observationTransactions := [];
  observationRawTransactions := [];
  observationWithdrawals := [];
  observationBlobGasUsed := 8;
  observationExcessBlobGas := 9;
  observationSlotNumber := None;
  observationBlockAccessList := [];
  observationParentBeaconRoot := repeat 0 32;
  observationVersionedHashes := [];
  observationDeposits := [];
  observationWithdrawalRequests := [];
  observationConsolidations := [];
  observationBuilderDeposits := [];
  observationBuilderExits := [];
  observationWitnessNodes := [];
  observationWitnessCodes := [];
  observationWitnessHeaders := [];
  observationChainId := 1;
  observationForkName := None;
  observationActiveForkIndex := 0;
  observationActivationBlock := None;
  observationActivationTimestamp := None;
  observationPublicKeys := [[1; 2]; [3]]
|}.

Definition writeSuccessCp1Observation : WriteSuccessObservation :=
  writeSuccessCp1ObservationWithBaseFee 7.

Example writeSuccessWrongMagicRejected :
  writeSuccessDecodeObservation
    (0 :: skipn 1 (writeSuccessEncodeObservation writeSuccessCp1Observation)) =
  None.
Proof. native_compute. reflexivity. Qed.

Example writeSuccessWrongVersionRejected :
  writeSuccessDecodeObservation
    (firstn 4 (writeSuccessEncodeObservation writeSuccessCp1Observation) ++
     [2] ++ skipn 5
       (writeSuccessEncodeObservation writeSuccessCp1Observation)) = None.
Proof. native_compute. reflexivity. Qed.

Example writeSuccessWrongSuccessByteRejected :
  writeSuccessDecodeObservation
    (firstn 5 (writeSuccessEncodeObservation writeSuccessCp1Observation) ++
     [0] ++ skipn 6
       (writeSuccessEncodeObservation writeSuccessCp1Observation)) = None.
Proof. native_compute. reflexivity. Qed.
