(* The chain end of post-withdrawals: the frozen entry trace, stated in
   the form the block emits.

   The post-withdrawals chain meets a hand-written predicate at its entry
   `0x156e8`, whose trace is `writeSuccessExactPostWithdrawalsEvents
   witness`. That trace does not reduce to its first write: its payload
   list is `drop (length … + …) (map …)` over abstract witness fields.
   `infer_trace.py` states the same first write as the block emits it
   (round 2 of `trace_post_withdrawals`). This lemma says the two are
   equal once the tail is the frozen trace's own tail, so the generated
   segment can state its entry in the inferred form, and composition at
   the chain end is one rewrite. *)

Require Import isla.isla.
Require Import ZesuSsz.Automation.All.
Require Import ZesuSsz.Contracts.Endpoints.
Require Import ZesuSsz.Contracts.IslarisCode.
Require Import ZesuSsz.Proofs.WriteSuccess.Interfaces.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessNativeContract.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessRepresentation.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessValueSpec.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessObservation.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessOutputSemantic.

Definition writeSuccessExactPostWithdrawalsInferredEvents {Decoded}
    (witness : writeSuccessNativeWitness Decoded) (tail : spec) : spec :=
  (Snapshots.writeOutputEvents (writeSuccessEntrySp witness - (2000 + 16)) 8 [Z_to_bv 8 (bv_unsigned (default (BV 64 0) (take 69 (writeSuccessValues witness) !! Z.to_nat ((bv_unsigned (writeSuccessFrameSp witness + 1136) - (bv_unsigned (writeSuccessFrameSp witness) + 1032)) `div` 8))) `mod` 256); Z_to_bv 8 ((bv_unsigned (default (BV 64 0) (take 69 (writeSuccessValues witness) !! Z.to_nat ((bv_unsigned (writeSuccessFrameSp witness + 1136) - (bv_unsigned (writeSuccessFrameSp witness) + 1032)) `div` 8))) `div` 256) `mod` 256); Z_to_bv 8 (((bv_unsigned (default (BV 64 0) (take 69 (writeSuccessValues witness) !! Z.to_nat ((bv_unsigned (writeSuccessFrameSp witness + 1136) - (bv_unsigned (writeSuccessFrameSp witness) + 1032)) `div` 8))) `div` 256) `div` 256) `mod` 256); Z_to_bv 8 ((((bv_unsigned (default (BV 64 0) (take 69 (writeSuccessValues witness) !! Z.to_nat ((bv_unsigned (writeSuccessFrameSp witness + 1136) - (bv_unsigned (writeSuccessFrameSp witness) + 1032)) `div` 8))) `div` 256) `div` 256) `div` 256) `mod` 256); Z_to_bv 8 (((((bv_unsigned (default (BV 64 0) (take 69 (writeSuccessValues witness) !! Z.to_nat ((bv_unsigned (writeSuccessFrameSp witness + 1136) - (bv_unsigned (writeSuccessFrameSp witness) + 1032)) `div` 8))) `div` 256) `div` 256) `div` 256) `div` 256) `mod` 256); Z_to_bv 8 ((((((bv_unsigned (default (BV 64 0) (take 69 (writeSuccessValues witness) !! Z.to_nat ((bv_unsigned (writeSuccessFrameSp witness + 1136) - (bv_unsigned (writeSuccessFrameSp witness) + 1032)) `div` 8))) `div` 256) `div` 256) `div` 256) `div` 256) `div` 256) `mod` 256); Z_to_bv 8 (((((((bv_unsigned (default (BV 64 0) (take 69 (writeSuccessValues witness) !! Z.to_nat ((bv_unsigned (writeSuccessFrameSp witness + 1136) - (bv_unsigned (writeSuccessFrameSp witness) + 1032)) `div` 8))) `div` 256) `div` 256) `div` 256) `div` 256) `div` 256) `div` 256) `mod` 256); Z_to_bv 8 ((((((((bv_unsigned (default (BV 64 0) (take 69 (writeSuccessValues witness) !! Z.to_nat ((bv_unsigned (writeSuccessFrameSp witness + 1136) - (bv_unsigned (writeSuccessFrameSp witness) + 1032)) `div` 8))) `div` 256) `div` 256) `div` 256) `div` 256) `div` 256) `div` 256) `div` 256) `mod` 256)] tail).

Lemma write_success_exact_post_withdrawals_chain_end {Decoded}
    `{!WriteSuccessMemoryRepresentation Decoded}
    (args : WriteSuccessArgs Decoded)
    (witness : writeSuccessNativeWitness Decoded)
    (Hwf : writeSuccessWitnessWellFormed args witness) :
  writeSuccessExactPostWithdrawalsEvents witness =
    writeSuccessExactPostWithdrawalsInferredEvents witness
      (exactPostWithdrawalsFirstTail witness).
Proof.
  rewrite exact_post_withdrawals_first_tail_explicit.
  unfold writeSuccessWitnessWellFormed in Hwf. destruct_and! Hwf.
  have Hindex : Z.to_nat ((bv_unsigned (writeSuccessFrameSp witness + 1136) -
      (bv_unsigned (writeSuccessFrameSp witness) + 1032)) `div` 8) = 13%nat.
  { unfold writeSuccessFrameSp. cbn in *. bv_simplify. bv_solve. }
  unfold writeSuccessExactPostWithdrawalsInferredEvents.
  rewrite Hindex lookup_take; [|lia].
  unfold writeSuccessValueWord, writeSuccessPrivateBytes, writeSuccessEncodeU64.
  f_equal. unfold writeSuccessFrameSp. bv_solve.
Qed.

Print Assumptions write_success_exact_post_withdrawals_chain_end.
