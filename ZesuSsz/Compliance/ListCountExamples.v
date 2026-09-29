From Coq Require Import Lia Lists.List ZArith.ZArith.
Require Import ZesuSsz.Compliance.BugPredicates.
Require Import ZesuSsz.Compliance.Targets.
Require Import ZesuSsz.Contracts.Endpoints.

Import ListNotations.
Open Scope Z_scope.

(** Use a binary offset accumulator to avoid repeated unary conversions. *)
Fixpoint zesuRepeatedOffsets (count : nat) (offset width : Z)
    (acc : ByteString) : ByteString :=
  match count with
  | O => rev_append acc []
  | S rest => zesuRepeatedOffsets rest (offset + width) width
                (rev_append (zesuEncodeLe 4 offset) acc)
  end.

(** Encode equal-sized byte lists with their SSZ offset table. *)
Definition zesuEncodeRepeatedByteList (count : nat) (item : ByteString) : ByteString :=
  zesuRepeatedOffsets count (4 * Z.of_nat count) (Z.of_nat (length item)) [] ++
  concat (repeat item count).

(** Legacy RLP: nonce, gas price, gas limit, recipient, value, data,
    v = 27, r, s.  Empty integer fields encode zero. *)
Definition zesuCountWitnessTransaction : ByteString :=
  [201; 128; 128; 128; 128; 128; 128; 27; 128; 128].

Definition zesuListCountWitnessPayload
    (transactions withdrawals : ByteString) : ByteString :=
  repeat 0 436 ++ zesuEncodeLe 4 540 ++ repeat 0 64 ++
  zesuEncodeLe 4 540 ++
  zesuEncodeLe 4 (540 + Z.of_nat (length transactions)) ++ repeat 0 16 ++
  zesuEncodeLe 4 (540 + Z.of_nat (length transactions) +
    Z.of_nat (length withdrawals)) ++ repeat 0 8 ++ transactions ++ withdrawals.

(** Use the V4 payload, five request offsets, chain ID one, and activation zero.
    These inputs isolate the new count domains from the seven original domains. *)
Definition zesuListCountWitnessInput
    (transactions withdrawals headers : ByteString) : ByteString :=
  let payload := zesuListCountWitnessPayload transactions withdrawals in
  let npr := zesuEncodeLe 4 44 ++
    zesuEncodeLe 4 (44 + Z.of_nat (length payload)) ++ repeat 0 32 ++
    zesuEncodeLe 4 (76 + Z.of_nat (length payload)) ++ payload ++
    repeat 0 32 ++ concat (repeat (zesuEncodeLe 4 20) 5) in
  let witness := concat (repeat (zesuEncodeLe 4 12) 3) ++ headers in
  [21; 1] ++ zesuEncodeLe 4 16 ++
  zesuEncodeLe 4 (16 + Z.of_nat (length npr)) ++
  zesuEncodeLe 4 (16 + Z.of_nat (length npr) + Z.of_nat (length witness)) ++
  zesuEncodeLe 4 (56 + Z.of_nat (length npr) + Z.of_nat (length witness)) ++
  npr ++ witness ++ zesuEncodeLe 8 1 ++ zesuEncodeLe 4 12 ++
  zesuEncodeLe 4 4 ++ zesuEncodeLe 4 8 ++ zesuEncodeLe 4 16 ++
  zesuEncodeLe 8 0 ++ zesuEncodeLe 8 0.

Definition withdrawalCountWitnessInput : ByteString :=
  zesuListCountWitnessInput [] (repeat 0 (17 * 44)) [].

Definition transactionCountWitnessInput : ByteString :=
  zesuListCountWitnessInput
    (zesuEncodeRepeatedByteList 1048577 zesuCountWitnessTransaction) [] [].

Definition witnessHeaderCountWitnessInput : ByteString :=
  zesuListCountWitnessInput [] [] (zesuEncodeRepeatedByteList 257 []).

(** These computations check the count mismatch.  They do not assert machine
    execution or evaluate the abstract reference decoder. *)
Lemma withdrawalCountMismatch decoded :
  zesuListCountLayout withdrawalCountWitnessInput =
    Some {| bugWithdrawalBytes := 748;
            bugTransactionCount := 0; bugWitnessHeaderCount := 0 |} /\
  withdrawalCountApplies withdrawalCountWitnessInput (DecodeSuccess decoded) /\
  (17 <=? 16) = false.
Proof. native_compute. repeat split; reflexivity. Qed.
Print Assumptions withdrawalCountMismatch.

(** The reference checks this count before it reads any transaction item.
    The evidence test checks the complete encoded witness and every RLP item. *)
Lemma transactionCountPrefixMismatch :
  zesuVariableListCount (zesuEncodeLe 4 4194308) 0 14680078 = Some 1048577 /\
  (1048577 <=? 1048576) = false.
Proof. native_compute. split; reflexivity. Qed.
Print Assumptions transactionCountPrefixMismatch.

Lemma witnessHeaderCountMismatch decoded :
  zesuListCountLayout witnessHeaderCountWitnessInput =
    Some {| bugWithdrawalBytes := 0;
            bugTransactionCount := 0; bugWitnessHeaderCount := 257 |} /\
  witnessHeaderCountApplies witnessHeaderCountWitnessInput (DecodeSuccess decoded) /\
  (257 <=? 256) = false.
Proof. native_compute. repeat split; reflexivity. Qed.
Print Assumptions witnessHeaderCountMismatch.

Lemma listCountNonVacuityLayout :
  zesuListCountLayout (zesuNonBugInput 21) =
    Some {| bugWithdrawalBytes := 0;
            bugTransactionCount := 0; bugWitnessHeaderCount := 0 |}.
Proof. native_compute. reflexivity. Qed.

Lemma listCountBugsNonVacuous actual :
  ~ withdrawalCountApplies (zesuNonBugInput 21) actual /\
  ~ transactionCountApplies (zesuNonBugInput 21) actual /\
  ~ witnessHeaderCountApplies (zesuNonBugInput 21) actual.
Proof.
  unfold withdrawalCountApplies, transactionCountApplies, witnessHeaderCountApplies.
  rewrite listCountNonVacuityLayout. destruct actual; cbn; repeat split; lia.
Qed.
Print Assumptions listCountBugsNonVacuous.
