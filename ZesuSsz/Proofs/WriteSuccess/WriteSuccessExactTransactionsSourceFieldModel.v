Require Import ZesuSsz.Automation.All.
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Export.Snapshots.
From Coq Require Import Lists.List.
From ZesuSsz.Proofs.WriteSuccess Require Import
  WriteSuccessTransactionsSpec WriteSuccessExactTransactionsLayout
  WriteSuccessExactTransactionsRowByte WriteSuccessExactTransactionsRowSlice
  WriteSuccessExactTransactionsSourceFieldEvents WriteSuccessExactTransactionsSourceFieldLayout
  WriteSuccessExactTransactionsRecipientSourceImage WriteSuccessExactTransactionsFlagLoads
  WriteSuccessExactTransactionsChainPriceFrame WriteSuccessExactTransactionsPriorityGasRegion
  WriteSuccessExactTransactionsRecipientBranchHandoff WriteSuccessExactTransactionsRecipientDataAccessRegion
  WriteSuccessExactTransactionsChainTailModel WriteSuccessExactTransactionsPriceTailModel
  WriteSuccessExactTransactionsGasTailModel WriteSuccessExactTransactionsRecipientTailModel
  WriteSuccessExactTransactionsDataTailModel WriteSuccessExactTransactionsAccessTailModel
  WriteSuccessExactTransactionsBlobCountTailModel WriteSuccessExactEncoderU128
  WriteSuccessExactEncoderU256Spec WriteSuccessExactBooleanSpec WriteSuccessExactStorageKeysModel
  WriteSuccessRepresentation WriteSuccessObservation WriteSuccessOutputSemantic.

Lemma transactions_source_field_model sp prefix transaction rest tail :
  Forall writeSuccessTransactionValid prefix ->
  writeSuccessTransactionValid transaction ->
  transactionSourceAfterChainEvents sp
    (writeSuccessTransactionsBytes (prefix ++ transaction :: rest)) (288 * length prefix)
    (writeSuccessTransactionData transaction) (writeSuccessTransactionAccessEntries transaction)
    (writeSuccessExactTransactionAfterBlobCountEvents sp transaction tail) =
  writeSuccessExactTransactionAfterChainEvents sp transaction tail.
Proof.
  intros Hprefix Hvalid.
  have Hfull : (288 * length prefix + 288 <=
      length (writeSuccessTransactionsBytes (prefix ++ transaction :: rest)))%nat.
  { rewrite exact_transactions_bytes_app app_length
      (exact_transactions_bytes_length prefix Hprefix).
    cbn [writeSuccessTransactionsBytes]. rewrite app_length (proj1 Hvalid). lia. }
  have Hbyte offset (Hoffset : (offset < 288)%nat) :
      transactionRowByte (writeSuccessTransactionsBytes (prefix ++ transaction :: rest))
        (288 * length prefix) offset = bv_zero_extend 64 (writeSuccessTransactionByte transaction offset).
  { rewrite exact_transaction_row_byte_extend; last lia.
    rewrite (exact_transaction_row_byte prefix transaction rest offset Hprefix Hvalid Hoffset).
    reflexivity. }
  have Himage := transactions_recipient_source_image
    (writeSuccessTransactionsBytes (prefix ++ transaction :: rest)) (288 * length prefix) Hfull.
  rewrite (exact_transaction_row_slice prefix transaction rest 265 20 Hprefix Hvalid ltac:(lia)) in Himage.
  have Hzero (byte : bv 8) : bv_zero_extend 64 byte = BV 64 0 <-> byte = BV 8 0.
  { split.
    - intros Heq. apply bv_eq. apply (f_equal bv_unsigned) in Heq.
      rewrite bv_zero_extend_unsigned in Heq; [exact Heq | done].
    - intros ->. apply bv_eq. rewrite bv_zero_extend_unsigned; done. }
  have HvalidCopy := Hvalid.
  destruct HvalidCopy as (Hlength & Htype & Hchain & Hnonce & Hgas & Hfee & Hlimit & Hto &
    Hvalue & HdataPointer & HdataLength & HaccessPointer & HaccessCount & HaccessBytes &
    HblobPointer & HblobCount & Hrest).
  have Hsize : writeSuccessTransactionWord transaction 200 =
      Z_to_bv 64 (Z.of_nat (length (writeSuccessTransactionData transaction))).
  { rewrite -HdataLength Z_to_bv_bv_unsigned. reflexivity. }
  rewrite transactions_exact_price_tail transactions_exact_gas_tail
    transactions_exact_recipient_tail transactions_exact_data_tail
    transactions_exact_access_tail transactions_exact_blob_count_tail.
  unfold transactionSourceAfterChainEvents, transactionNoncePricePriorityOutputTrace,
    transactionPriorityGasTrace, transactionRecipientValueTrace, transactionDataAccessOutputTrace.
  rewrite !(exact_transaction_row_word prefix transaction rest _ Hprefix Hvalid); [|lia..].
  rewrite (Hbyte 32%nat ltac:(lia)) (Hbyte 285%nat ltac:(lia)) Hnonce Hlimit
    HdataPointer HdataLength Hsize HaccessCount HblobCount -Hgas Hvalue.
  rewrite !writeSuccessU128WordsPayload_encoder writeSuccessU256WordsPayload_encoder
    !writeSuccessPrivatePublicBytes Himage.
  cbn [writeSuccessPairValue writeSuccessWordsValue].
  rewrite Z.mul_0_r Z.add_0_r.
  destruct (writeSuccessTransactionGasPriorityFee transaction) as [fee|] eqn:HfeeOption;
    destruct (writeSuccessTransactionTo transaction) as [address|] eqn:HtoOption;
    cbn in Hfee, Hto.
  all: lazymatch type of Hfee with
    | _ /\ _ => destruct Hfee as [HfeeTag HfeeWords]
    | _ => idtac
    end.
  all: lazymatch type of Hto with
    | _ /\ _ => destruct Hto as [HtoTag [Haddress HaddressLength]]
    | _ => idtac
    end.
  all: try rewrite -HfeeWords.
  all: try rewrite Haddress.
  all: repeat first
    [ rewrite bool_decide_true; last (apply Hzero; assumption)
    | rewrite bool_decide_false; last (intros H; apply Hzero in H; contradiction) ].
  all: try rewrite (writeSuccessBooleanWordPayload_encoder true).
  all: try rewrite (writeSuccessBooleanWordPayload_encoder false).
  all: try rewrite !writeSuccessPrivatePublicBytes.
  all: unfold writeSuccessPublicBytes; rewrite !map_length.
  all: cbn [writeSuccessPairValue].
  all: reflexivity.
Qed.
Print Assumptions transactions_source_field_model.
