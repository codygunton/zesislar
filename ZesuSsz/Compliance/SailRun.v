From Coq Require Import List String ZArith.
Require Import SailStdpp.MachineWord SailStdpp.Values SailStdpp.Prompt_monad.
Require Import SailStdpp.State_monad SailStdpp.State_lifting.
Require Import EvmSailRlp.evm_rlp_types EvmSailRlp.evm_rlp.
Require Import ZesuSsz.Compliance.RlpInputBounds.

(* Pinned EVM-Sail d0e4aabdde52f9158d191dbc8add444abffd9a6a.
   The only reachable fatal_error(RlpDecode) sites in these four roots are:
   sail/lib/rlp/decoding.sail:46
   sail/lib/rlp/decoding.sail:60
   sail/lib/rlp/decoding.sail:70
   sail/lib/rlp/decoding.sail:88
   sail/lib/rlp/decoding.sail:103
   sail/lib/rlp/decoding.sail:108
   sail/lib/rlp/decoding.sail:111
   sail/lib/rlp/decoding.sail:123
   sail/lib/rlp/decoding.sail:160
   sail/lib/rlp/decoding.sail:172
   sail/lib/rlp/decoding.sail:185
   sail/lib/rlp/decoding.sail:494
   sail/lib/rlp/decoding.sail:511
   sail/lib/rlp/decoding.sail:524
   sail/lib/ssz/stateless_input.sail:727
   sail/lib/ssz/stateless_input.sail:738
   sail/primitives/quantities.sail:607 is an assertion failure. It is
   UnsupportedOrInternalFailure, including when it occurs in a decoder.
   The pinned-source gate checks all 16 sites before this classification.
*)

Import ListNotations.
Open Scope string_scope.
Open Scope Z_scope.

Inductive SailOutcome (A : Type) : Type :=
| Success : A -> SailOutcome A
| Reject : FatalError -> SailOutcome A
| UnsupportedOrInternalFailure : string -> SailOutcome A.
Arguments Success {A} _.
Arguments Reject {A} _.
Arguments UnsupportedOrInternalFailure {A} _.

(* The input slice and its bounds are fixed before this interpreter runs.
   Register prompts are deterministic. Choose is unsupported. liftState
   resolves Choose through chooseS, so the evaluator does not take its first
   result. Excl_res and memory writes can invoke nondet_boolS in State_monad;
   this evaluator marks them unsupported before that operation runs. Memory
   reads, Write_ea, Write_tag, Footprint, Barrier, Print, and Exception are
   unsupported too. The generated RLP closure contains no Choose constructor.
*)
Fixpoint runPrompt {A} (m : M A) (rs : regstate) (allowExit : bool)
  {struct m} : SailOutcome A * regstate :=
  match m with
  | Done v => (Success v, rs)
  | Read_reg r k => runPrompt (k (register_lookup r rs)) rs allowExit
  | Write_reg r v k => runPrompt k (register_set r v rs) allowExit
  | Fail message =>
      (if andb allowExit (String.eqb message "exit")
       then Reject RlpDecode
       else UnsupportedOrInternalFailure message, rs)
  | Choose _ _ _ => (UnsupportedOrInternalFailure "nondeterministic choice", rs)
  | Exception _ => (UnsupportedOrInternalFailure "exception", rs)
  | Print _ _ => (UnsupportedOrInternalFailure "print effect", rs)
  | _ => (UnsupportedOrInternalFailure "unimplemented host effect", rs)
  end.

Definition classifiedResult {A} (o : SailOutcome A) :
    option (SailStdpp.State_monad.result A unit) :=
  match o with
  | Success v => Some (Value v)
  | Reject _ => Some (Ex (Failure "exit"))
  | UnsupportedOrInternalFailure _ => None
  end.

Lemma runPromptLiftState {A} (m : M A) (rs : regstate)
    (allowExit : bool) (o : SailOutcome A) (rs' : regstate)
    (choices : ChoiceSource) :
  runPrompt m rs allowExit = (o, rs') ->
  match classifiedResult o with
  | Some result => In (result, init_state rs', choices)
      (liftState register_accessors m (init_state rs) choices)
  | None => True
  end.
Proof.
  revert rs o rs'.
  induction m; intros rs o rs' Heval; simpl in Heval;
    try (inversion Heval; subst; simpl; exact I).
  - inversion Heval; subst. simpl. left. reflexivity.
  - specialize (H (register_lookup r rs) rs o rs' Heval).
    cbn [liftState bindS read_regvalS readS returnS register_accessors
         init_state ss_regstate List.flat_map List.app].
    destruct (classifiedResult o) as [result|]; simpl in *; auto.
    rewrite app_nil_r. exact H.
  - specialize (IHm (register_set r r0 rs) o rs' Heval).
    cbn [liftState seqS write_regvalS readS bindS returnS updateS
         register_accessors init_state ss_regstate ss_memstate ss_tagstate
         ss_output List.flat_map List.app].
    destruct (classifiedResult o) as [result|]; simpl in *; auto.
    rewrite app_nil_r. exact IHm.
  - destruct (andb allowExit (String.eqb s "exit")) eqn:Hexit;
      inversion Heval; subst; simpl; auto.
    apply Bool.andb_true_iff in Hexit as [_ Hmessage].
    apply String.eqb_eq in Hmessage. subst s.
    simpl. left. reflexivity.
Qed.

Local Definition runDecoder {A} (bytes : list byte) (base len : Z)
    (action : M A) : SailOutcome A :=
  if validInputSlice bytes base len then
    fst (runPrompt (SailStdpp.Prompt_monad.bind0 (initializedInput bytes) action)
                   init_regstate true)
  else UnsupportedOrInternalFailure "input slice outside backing bytes".

Definition runRlpDecodeItem {base len : Z} (bytes : list byte)
    (cursor : RlpCursor base len) :=
  runDecoder bytes base len (evm_rlp.rlp_decode_item cursor).

Definition runRlpRefHdr {base len : Z} (bytes : list byte)
    (cursor : StatelessInputSliceFields base len) :=
  runDecoder bytes base len (evm_rlp.rlp_ref_hdr cursor).

Definition runRlpNodeCursor {base len : Z} (bytes : list byte)
    (node : StatelessInputSliceFields base len) :=
  runDecoder bytes base len (evm_rlp.rlp_node_cursor node).

Definition runParentHeaderFields {base len : Z} (bytes : list byte)
    (cursor : StatelessInputSliceFields base len)
    (fieldIndex : parent_header_field_cursor) (fields : ParentHeaderFields) :=
  if (0 <=? parent_header_field_cursor_value fieldIndex) &&
     (parent_header_field_cursor_value fieldIndex <=? 19) then
    runDecoder bytes base len
      (evm_rlp.decode_parent_header_fields cursor fieldIndex fields)
  else UnsupportedOrInternalFailure "invalid parent-header field index".

(* These two integer decoders are subcalls of the audited
   decode_parent_header_fields root. Their direct RlpDecode sites are
   decoding.sail:511 and :524; rlp_decode_u256 also reaches :494 through
   rlp_decode_word. No additional fatal_error site enters this closure. *)
Definition runRlpDecodeU256 {base len contentLen : Z} (bytes : list byte)
    (field : RlpFieldRef base len contentLen) :=
  if (0 <=? contentLen) && (contentLen <=? len) then
    runDecoder bytes base len (evm_rlp.rlp_decode_u256 field)
  else UnsupportedOrInternalFailure "invalid RLP field content length".

Definition runRlpDecodeUint64 {base len contentLen : Z} (bytes : list byte)
    (field : RlpFieldRef base len contentLen) :=
  if (0 <=? contentLen) && (contentLen <=? len) then
    runDecoder bytes base len (evm_rlp.rlp_decode_uint64 field)
  else UnsupportedOrInternalFailure "invalid RLP field content length".

Example emptyRlpHeaderRejects :
  runRlpRefHdr [] (@Build_StatelessInputSliceFields 0 0 0 0) = Reject RlpDecode.
Proof. vm_compute. reflexivity. Qed.

Example invalidBackingIsUnsupported :
  runRlpRefHdr [] (@Build_StatelessInputSliceFields 1 0 1 0) =
    UnsupportedOrInternalFailure "input slice outside backing bytes".
Proof. vm_compute. reflexivity. Qed.

Example oneByteHeaderSucceeds :
  runRlpRefHdr [mword_of_int 1] (@Build_StatelessInputSliceFields 0 1 0 1) =
    Success (false, Build_source_pointer 0, 1).
Proof. vm_compute. reflexivity. Qed.
