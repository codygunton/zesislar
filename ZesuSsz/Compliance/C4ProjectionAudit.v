From Coq Require Import List ZArith.
Require Import EvmSail.evm_decoder_types.
Require Import ZesuSsz.Compliance.ProjectionTransaction.

(* The Q18 decoder stores the two Keccak results only in sender and
   signing_hash. This lemma covers the value projection after construction.
   It does not prove that the seven host actions complete or preserve input. *)
Definition replaceHashOutputs {limit : Z} (tx : TransactionFields limit)
    (sender : address_typ) (signingHash : hash) : TransactionFields limit :=
  {| TransactionFields_tx_type := tx.(TransactionFields_tx_type);
     TransactionFields_sender := sender;
     TransactionFields_nonce := tx.(TransactionFields_nonce);
     TransactionFields_chain_id := tx.(TransactionFields_chain_id);
     TransactionFields_gas_limit := tx.(TransactionFields_gas_limit);
     TransactionFields_is_create := tx.(TransactionFields_is_create);
     TransactionFields_recipient := tx.(TransactionFields_recipient);
     TransactionFields_value := tx.(TransactionFields_value);
     TransactionFields_raw := tx.(TransactionFields_raw);
     TransactionFields_input_src := tx.(TransactionFields_input_src);
     TransactionFields_access_list := tx.(TransactionFields_access_list);
     TransactionFields_max_fee := tx.(TransactionFields_max_fee);
     TransactionFields_max_blob_fee := tx.(TransactionFields_max_blob_fee);
     TransactionFields_max_priority_fee := tx.(TransactionFields_max_priority_fee);
     TransactionFields_authorizations := tx.(TransactionFields_authorizations);
     TransactionFields_blob_hashes := tx.(TransactionFields_blob_hashes);
     TransactionFields_pubkey := tx.(TransactionFields_pubkey);
     TransactionFields_signing_hash := signingHash;
     TransactionFields_sig_v := tx.(TransactionFields_sig_v);
     TransactionFields_sig_r := tx.(TransactionFields_sig_r);
     TransactionFields_sig_s := tx.(TransactionFields_sig_s) |}.

Lemma transactionProjectionIgnoresHashOutputs {limit : Z}
    (backing rawBytes publicKeyBytes : list byte)
    (tx : TransactionFields limit) (zig : ProjectedTransaction)
    (sender : address_typ) (signingHash : hash) :
  TransactionProjection backing rawBytes publicKeyBytes
    (replaceHashOutputs tx sender signingHash) zig <->
  TransactionProjection backing rawBytes publicKeyBytes tx zig.
Proof.
  destruct tx; unfold replaceHashOutputs; simpl; tauto.
Qed.
