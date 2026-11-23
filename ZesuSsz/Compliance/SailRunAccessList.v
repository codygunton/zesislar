From Coq Require Import List String ZArith.
Require Import SailStdpp.MachineWord SailStdpp.Values SailStdpp.Prompt_monad.
Require Import EvmSailRlp.evm_rlp_types.
Require EvmSailTransactions.evm_decode_access_list_tx_types.
Require EvmSailTransactions.evm_decode_access_list_tx.
Require Import ZesuSsz.Compliance.RlpInputBounds ZesuSsz.Compliance.SailRun.

(* Pinned EVM-Sail d0e4aabdde52f9158d191dbc8add444abffd9a6a, as SailRun.
   This runner stays out of SailRun so that SailRun's dependents do not
   depend on the transaction closure. *)

Import ListNotations.
Open Scope string_scope.
Open Scope Z_scope.

(* decode_access_list (sail/lib/rlp/codecs/transactions.sail:89) lives in the
   generated transaction closure EvmSailTransactions. That closure has its own
   register type, so it gets its own prompt runner with the rules of
   runPrompt. Its reachable fatal_error(RlpDecode) sites are
   sail/lib/rlp/codecs/transactions.sail:103 (source above 2^30 bytes) and
   sail/lib/rlp/decoding.sail:46, 60, 70, 88, 103, 108, 111, 123, 147, 494.
   test_sail_fatal_sites.py pins both lists. Every fatal_error exits, so the
   runner reports each of them as Reject RlpDecode. *)
Fixpoint runAccessListPrompt {A}
    (m : evm_decode_access_list_tx_types.M A)
    (rs : evm_decode_access_list_tx_types.regstate) (allowExit : bool)
  {struct m} : SailOutcome A * evm_decode_access_list_tx_types.regstate :=
  match m with
  | Done v => (Success v, rs)
  | Read_reg r k =>
      runAccessListPrompt
        (k (evm_decode_access_list_tx_types.register_lookup r rs)) rs allowExit
  | Write_reg r v k =>
      runAccessListPrompt k
        (evm_decode_access_list_tx_types.register_set r v rs) allowExit
  | Fail message =>
      (if andb allowExit (String.eqb message "exit")
       then Reject RlpDecode
       else UnsupportedOrInternalFailure message, rs)
  | Choose _ _ _ => (UnsupportedOrInternalFailure "nondeterministic choice", rs)
  | Exception _ => (UnsupportedOrInternalFailure "exception", rs)
  | Print _ _ => (UnsupportedOrInternalFailure "print effect", rs)
  | _ => (UnsupportedOrInternalFailure "unimplemented host effect", rs)
  end.

(* As initializedInput: Sail initialization resets the input register, so
   the bytes are installed afterward. *)
Definition initializedAccessListInput (bytes : list byte) :
    evm_decode_access_list_tx_types.M unit :=
  SailStdpp.Prompt_monad.bind0 (evm_decode_access_list_tx.sail_model_init tt)
    (evm_decode_access_list_tx_types.write_reg
       (evm_decode_access_list_tx_types.R_list_byte
          evm_decode_access_list_tx_types.shim_input_bytes) bytes).

Definition runDecodeAccessList {base len contentLen : Z} (bytes : list byte)
    (field : evm_decode_access_list_tx_types.RlpFieldRef base len contentLen) :
    SailOutcome evm_decode_access_list_tx_types.AccessListRef :=
  if validInputSlice bytes base len && (0 <=? contentLen) &&
     (contentLen <=? len) then
    fst (runAccessListPrompt
           (SailStdpp.Prompt_monad.bind0 (initializedAccessListInput bytes)
              (evm_decode_access_list_tx.decode_access_list field))
           evm_decode_access_list_tx_types.init_regstate true)
  else UnsupportedOrInternalFailure "invalid access-list field or input slice".

Definition accessListCounts
    (o : SailOutcome evm_decode_access_list_tx_types.AccessListRef) :
    option (Z * Z) :=
  match o with
  | Success r =>
      Some (evm_decode_access_list_tx_types.transaction_item_count_value
              (evm_decode_access_list_tx_types.AccessListRef_address_count r),
            evm_decode_access_list_tx_types.transaction_item_count_value
              (evm_decode_access_list_tx_types.AccessListRef_slot_count r))
  | _ => None
  end.

(* The list item that spans the whole input slice [0, len). *)
Definition wholeInputList (len contentLen : Z) :
    evm_decode_access_list_tx_types.RlpFieldRef 0 len contentLen :=
  @evm_decode_access_list_tx_types.Build_RlpFieldRef 0 len contentLen
    (@evm_decode_access_list_tx_types.Build_StatelessInputSliceFields 0 len 0 len)
    true contentLen.

Example emptyAccessListCounts :
  accessListCounts
    (runDecodeAccessList [mword_of_int 192] (wholeInputList 1 0)) = Some (0, 0).
Proof. vm_compute. reflexivity. Qed.

(* [[20 bytes, [32 bytes]]]: f8 38 f7 94 <20 bytes> e1 a0 <32 bytes>. *)
Example oneEntryOneKeyAccessListCounts :
  accessListCounts
    (runDecodeAccessList
       (app [mword_of_int 248; mword_of_int 56; mword_of_int 247; mword_of_int 148]
          (app (List.repeat (mword_of_int 17) 20)
             (app [mword_of_int 225; mword_of_int 160]
                (List.repeat (mword_of_int 34) 32))))
       (wholeInputList 58 56)) = Some (1, 1).
Proof. vm_compute. reflexivity. Qed.
