From stdpp Require Import base list bitvector.definitions.
Require Import ZesuSsz.Automation2.CallSliceInterface.
Require Import ZesuSsz.Contracts.DecodeItemPayloadBounds.
Require Import ZesuSsz.Contracts.DecodeItemCallFacts.
Require Import ZesuSsz.Contracts.DecodeItemCallData.
Require Import ZesuSsz.Interfaces.DecodeItem.
Local Open Scope Z_scope.

(* decodeItem as the callee of the call-site step (`Automation2/CallSlice.v`):
   its argument record, its 40-byte output slot, the outcome words that name
   the payload and the consumed count, and the four interface lemmas. *)
#[export] Instance decodeItemCallSliceInterface :
    ZesuCallSliceInterface decodeItemCallDomain decodeItemCallMeaning := {|
  zesu_call_slice_args := decodeItemCallDataArgs;
  zesu_call_slice_out_size := 40%nat;
  zesu_call_slice_payload_pointer after := listWord64At0 after;
  zesu_call_slice_payload_pointer_load after := leWord64 after 0;
  zesu_call_slice_payload_length after := listWord64At8 after;
  zesu_call_slice_consumed after := listWord64At24 after;
  zesu_call_slice_payload_limit := 18446744073709551607;
  zesu_call_slice_domain_input := decodeItemCallDomainInput;
  zesu_call_slice_consumed_le := decodeItemCallConsumed;
  zesu_call_slice_payload_in_input := decodeItemCallPayloadInInput;
  zesu_call_slice_payload_in_input_load := decodeItemCallPayloadInInputLe |}.
