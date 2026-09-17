Require Import ZesuSsz.Automation.All.
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Contracts.Endpoints.
From Coq Require Import Lists.List ZArith.ZArith.
From ZesuSsz.Proofs.WriteSuccess Require Import
  FixedRowsChunks Interfaces WriteSuccessExactTailWithdrawalCountModel
  WriteSuccessEncodeFragments
  WriteSuccessExactPrefixStackFacts WriteSuccessExactTailStackCallBounds
  WriteSuccessExactTrace
  WriteSuccessExactWithdrawalsLoopSpec WriteSuccessExactWithdrawalsModel WriteSuccessNativeContract
  WriteSuccessOutputSemantic WriteSuccessPrivatePublicBytes
  WriteSuccessRepresentation WriteSuccessValueSpec.

Definition writeSuccessExactWithdrawalRows {Decoded}
    (witness : writeSuccessNativeWitness Decoded) : list (list (bv 8)) :=
  reshape (replicate (writeSuccessWithdrawalsCount witness) 48%nat)
    (writeSuccessWithdrawalsBytes witness).

Lemma concat_reshape_replicate {A} width count (values : list A) :
  length values = (count * width)%nat ->
  concat (reshape (replicate count width) values) = values.
Proof.
  revert values. induction count as [|count IH]; intros values Hlength.
  - apply length_zero_iff_nil in Hlength. subst values. reflexivity.
  - cbn [reshape replicate concat]. rewrite IH.
    + apply take_drop.
    + rewrite length_drop. lia.
Qed.

Lemma write_success_exact_withdrawal_rows_facts {Decoded}
    `{!WriteSuccessMemoryRepresentation Decoded}
    (args : WriteSuccessArgs Decoded)
    (witness : writeSuccessNativeWitness Decoded) :
  writeSuccessWitnessWellFormed args witness ->
  let rows := writeSuccessExactWithdrawalRows witness in
  length rows = writeSuccessWithdrawalsCount witness /\
  Forall (fun row => length row = 48%nat) rows /\
  concat rows = writeSuccessWithdrawalsBytes witness.
Proof.
  intros Hwf rows. unfold writeSuccessExactWithdrawalRows in rows.
  have Hlength : length (writeSuccessWithdrawalsBytes witness) =
      (48 * writeSuccessWithdrawalsCount witness)%nat by
    (unfold writeSuccessWitnessWellFormed in Hwf; tauto).
  subst rows. split.
  - rewrite length_reshape length_replicate. reflexivity.
  - split.
    + apply Forall_lookup. intros index row Hrow.
      rewrite sublist_lookup_reshape in Hrow; [|lia|lia].
      exact (sublist_lookup_length _ _ _ _ Hrow).
    + apply concat_reshape_replicate. lia.
Qed.

Lemma write_success_exact_withdrawal_rows_native {Decoded}
    `{!WriteSuccessMemoryRepresentation Decoded}
    (args : WriteSuccessArgs Decoded)
    (witness : writeSuccessNativeWitness Decoded) :
  writeSuccessWitnessWellFormed args witness ->
  let rows := writeSuccessExactWithdrawalRows witness in
  map (fun index => take 48 (drop (48 * index)
      (writeSuccessWithdrawalsBytes witness)))
    (seq 0 (writeSuccessWithdrawalsCount witness)) = rows.
Proof.
  intros Hwf rows.
  have [Hcount [Hall Hconcat]] :=
    write_success_exact_withdrawal_rows_facts args witness Hwf.
  have Hchunks := fixed_rows_chunks 48 rows Hall.
  rewrite Hconcat Hcount in Hchunks.
  unfold writeSuccessFixedChunks, writeSuccessBytesAt in Hchunks.
  rewrite !map_map in Hchunks.
  have Hnative :
      map (fun index => writeSuccessPrivateBytes (writeSuccessPublicBytes
        (take 48 (drop (48 * index) (writeSuccessWithdrawalsBytes witness)))))
        (seq 0 (writeSuccessWithdrawalsCount witness)) =
      map (fun index => take 48 (drop (48 * index)
        (writeSuccessWithdrawalsBytes witness)))
        (seq 0 (writeSuccessWithdrawalsCount witness)).
  { apply map_ext. intros index. apply writeSuccessPrivatePublicBytes. }
  rewrite Hnative in Hchunks.
  exact Hchunks.
Qed.

Lemma exact_tail_after_withdrawal_count_rows {Decoded}
    `{!WriteSuccessMemoryRepresentation Decoded}
    (args : WriteSuccessArgs Decoded)
    (witness : writeSuccessNativeWitness Decoded) :
  writeSuccessWitnessWellFormed args witness ->
  exactTailAfterWithdrawalCountEvents witness =
    writeSuccessExactWithdrawalEvents (writeSuccessFrameSp witness)
      (writeSuccessExactWithdrawalRows witness)
      (writeSuccessExactPostWithdrawalsEvents witness).
Proof.
  intros Hwf.
  have [Hcount [Hall Hconcat]] :=
    write_success_exact_withdrawal_rows_facts args witness Hwf.
  have Hrows := write_success_exact_withdrawal_rows_native args witness Hwf.
  rewrite withdrawal_rows_events_canonical.
  unfold exactTailAfterWithdrawalCountEvents,
    writeSuccessExactPostWithdrawalsEvents.
  cbn [writeSuccessExactObservation writeSuccessNativeObservation].
  rewrite Hcount -Hrows exact_post_withdrawals_payloads.
  rewrite writeOutputPayloadsSpec_app.
  2: rewrite writeSuccessWithdrawalsItemDescriptors_length map_length
       (concat_map_constant_length writeSuccessWithdrawalFragments 4);
     [rewrite exact_observation_withdrawals_length; lia | intros; reflexivity].
  reflexivity.
Qed.

Lemma write_success_exact_withdrawal_initial_facts {Decoded}
    `{!WriteSuccessMemoryRepresentation Decoded}
    (args : WriteSuccessArgs Decoded)
    (witness : writeSuccessNativeWitness Decoded) :
  writeSuccessWitnessWellFormed args witness ->
  0 < writeSuccessWithdrawalsCount witness ->
  exists row rest,
    writeSuccessExactWithdrawalRows witness = row :: rest /\
    withdrawalLoopFacts (writeSuccessFrameSp witness)
      (Z_to_bv 64 (bv_unsigned (writeSuccessWithdrawalsBase witness)))
      (bv_unsigned (writeSuccessWithdrawalsBase witness))
      (row :: rest) [] row rest (writeSuccessWithdrawalsBytes witness).
Proof.
  intros Hwf Hpositive.
  have [Hcount [Hall Hconcat]] :=
    write_success_exact_withdrawal_rows_facts args witness Hwf.
  destruct (writeSuccessExactWithdrawalRows witness) as [|row rest] eqn:Hrows;
    [cbn in Hcount; lia|].
  exists row, rest. split; first reflexivity.
  have [HstackLow _] := exact_tail_stack_call_bounds args witness Hwf.
  have [_ [Halign HstackHigh]] := exact_prefix_stack_facts args witness Hwf.
  have HcountWord := exact_tail_withdrawal_count_word args witness Hwf.
  have HbaseLow : mapRamBase defaultMap <=
      bv_unsigned (writeSuccessWithdrawalsBase witness) by
    (unfold writeSuccessWitnessWellFormed in Hwf; tauto).
  have HbaseHigh : bv_unsigned (writeSuccessWithdrawalsBase witness) +
      Z.of_nat (length (writeSuccessWithdrawalsBytes witness)) <
      machineRamEnd defaultMap by
    (unfold writeSuccessWitnessWellFormed in Hwf; tauto).
  unfold withdrawalLoopFacts. repeat split.
  - exact Hall.
  - symmetry. exact Hconcat.
  - bv_solve.
  - cbn in Hcount.
    rewrite Hcount -HcountWord.
    exact (proj2 (bv_unsigned_in_range 64
      (writeSuccessValueWord (writeSuccessValues witness) 12))).
  - exact Halign.
  - lia.
  - exact HstackHigh.
  - exact HbaseLow.
  - exact HbaseHigh.
Qed.

Print Assumptions write_success_exact_withdrawal_rows_facts.
Print Assumptions write_success_exact_withdrawal_rows_native.
Print Assumptions exact_tail_after_withdrawal_count_rows.
Print Assumptions write_success_exact_withdrawal_initial_facts.
