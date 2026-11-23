From Coq Require Import Bool List String ZArith Zwf.
From stdpp Require Import base decidable bitvector.definitions.
Require Import SailStdpp.MachineWord SailStdpp.Values SailStdpp.Prompt_monad.
Require Import EvmSailRlp.evm_rlp_types.
Require EvmSailTransactions.evm_decode_access_list_tx_types.
Require EvmSailTransactions.evm_decode_access_list_tx.
Require Import ZesuSsz.Compliance.RlpInputBounds.
Require Import ZesuSsz.Compliance.SailRun.
Require Import ZesuSsz.Compliance.SailRunAccessList.
Require Import ZesuSsz.Contracts.RlpDecodeItem.
Require Import ZesuSsz.Contracts.Candidates.AccessListCandidate.
Require Import ZesuSsz.Contracts.TxAccessListBugTriggers.
Require Import ZesuSsz.Contracts.TxAccessListMeaning.

Open Scope Z_scope.

(* Plan B6, decision step: the statements of the Sail agreement of
   rlp_decode.txAccessList, one `<lemma>_statement : Prop` per obligation
   `txAccessList/meaning/<lemma>`, with no proof. Owner: Sail agreement
   statement (review packet b6-sail). Generated with the goal directories
   from one lemma list (_build/agents/aa/b6-sail/spec.py); the order below is
   a dependency order.

   Layers:
   - M: the access-list prompt runner (runAccessListPrompt) through bind,
     assert, fatal_error, the input shim, and initialization.
   - L: input windows (alWindow): sub-slices and cursor advances.
   - W: each Sail function that decode_access_list reaches, run on a slice
     whose bytes are installed, equals a pure model on the slice's window:
     alSailHdr, alSailItem, alSailKeys, alSailEntries (the Sail recursions
     rendered as list functions with nat fuel). The Sail recursion limit is
     the slice length and each item consumes at least one byte, so no
     "recursion limit reached" assert fails; every slice stays inside the
     installed bytes, so no backing assert fails: every Sail run is Success
     or Reject RlpDecode, never UnsupportedOrInternalFailure.
   - P: the pure Sail model against the candidate (AccessListCandidate.v):
     equal, or a reached call hits a proposed trigger (D1 address length,
     D2 key length, D3 entry trailing bytes; TxAccessListBugTriggers.v).
   - C: txAccessListSailAgreesModuloProposed, the "Sail agrees" disjunct of
     TxAccessListMeaningModuloKnownBugs with the proposed triggers in place
     of the registered KnownBug classes (none registered yet). *)

Module ALT := EvmSailTransactions.evm_decode_access_list_tx_types.
Module ALS := EvmSailTransactions.evm_decode_access_list_tx.

(* ---- runner state and windows ---- *)

Definition alRegs (rs : ALT.regstate) (bytes : list byte) : Prop :=
  ALT.register_lookup (ALT.R_list_byte ALT.shim_input_bytes) rs = bytes.

Definition alSliceIn (bytes : list byte) (base len : Z) : Prop :=
  0 <= base /\ 0 <= len /\ base + len <= Z.of_nat (List.length bytes).

#[local] Instance alSliceIn_dec bytes base len : Decision (alSliceIn bytes base len).
Proof. unfold alSliceIn. apply _. Defined.

Definition alWindow (bytes : list byte) (base len : Z) : list byte :=
  firstn (Z.to_nat len) (skipn (Z.to_nat base) bytes).

(* ---- pure Sail model ---- *)

(* rlp_ref_hdr on a window: (is_list, header length, payload length). *)
Definition alSailHdr (r : list byte) : option (bool * Z * Z) :=
  match r with
  | nil => None
  | prefix :: rest =>
      let h := bv_unsigned prefix in
      if h <? 128 then Some (false, 0, 1)
      else if h <? 184 then Some (false, 1, h - 128)
      else if h <? 192 then
        if h - 183 <=? Z.of_nat (List.length r) - 1
        then Some (false, 1 + (h - 183), bigEndian (firstn (Z.to_nat (h - 183)) rest))
        else None
      else if h <? 248 then Some (true, 1, h - 192)
      else if h - 247 <=? Z.of_nat (List.length r) - 1
        then Some (true, 1 + (h - 247), bigEndian (firstn (Z.to_nat (h - 247)) rest))
        else None
  end.

Definition alHdrOutcome (o : option (bool * Z * Z))
    : SailOutcome (bool * ALT.source_pointer * Z) :=
  match o with
  | Some (isList, h, p) => Success (isList, ALT.Build_source_pointer h, p)
  | None => Reject RlpDecode
  end.

(* rlp_decode_item on a window: the header and the fit check. *)
Definition alSailItem (r : list byte) : option (bool * Z * Z) :=
  match alSailHdr r with
  | Some (isList, h, p) =>
      if h + p <=? Z.of_nat (List.length r) then Some (isList, h, p) else None
  | None => None
  end.

(* The bytes after one item (rlp_cursor_advance). *)
Definition alSkip (r : list byte) (h p : Z) : list byte :=
  skipn (Z.to_nat (h + p)) r.

(* _rec_decode_access_list_keys: the number of keys. *)
Fixpoint alSailKeysFuel (fuel : nat) (keys : list byte) : option Z :=
  match keys with
  | nil => Some 0
  | _ :: _ =>
      match fuel with
      | O => None
      | S fuel' =>
          match alSailItem keys with
          | Some (false, h, p) =>
              if p <=? 32 then option_map (Z.add 1) (alSailKeysFuel fuel' (alSkip keys h p))
              else None
          | _ => None
          end
      end
  end.

Definition alSailKeys (keys : list byte) : option Z :=
  alSailKeysFuel (List.length keys) keys.

(* One entry of _rec_decode_access_list_entries: the address item, the keys
   item, expect_end, rlp_decode_word of the address, rlp_decode_list of the
   keys, and the keys walk; the number of keys. *)
Definition alSailEntry (fields : list byte) : option Z :=
  match alSailItem fields with
  | Some (addressIsList, addressHeader, addressLength) =>
      let afterAddress := alSkip fields addressHeader addressLength in
      match alSailItem afterAddress with
      | Some (keysIsList, keysHeader, keysLength) =>
          if negb (Nat.eqb (List.length (alSkip afterAddress keysHeader keysLength)) 0) then None
          else if addressIsList || (32 <? addressLength) then None
          else if keysIsList then alSailKeys (alWindow afterAddress keysHeader keysLength)
          else None
      | None => None
      end
  | None => None
  end.

(* _rec_decode_access_list_entries: (address count, slot count). *)
Fixpoint alSailEntriesFuel (fuel : nat) (entries : list byte) : option (Z * Z) :=
  match entries with
  | nil => Some (0, 0)
  | _ :: _ =>
      match fuel with
      | O => None
      | S fuel' =>
          match alSailItem entries with
          | Some (true, h, p) =>
              match alSailEntry (alWindow entries h p), alSailEntriesFuel fuel' (alSkip entries h p) with
              | Some keys, Some (addresses, slots) => Some (addresses + 1, slots + keys)
              | _, _ => None
              end
          | _ => None
          end
      end
  end.

Definition alSailEntries (entries : list byte) : option (Z * Z) :=
  alSailEntriesFuel (List.length entries) entries.

(* decode_access_list on the first item of the input: the 2^30 guard, the
   list check, and the entries walk over the payload. *)
Definition alSailTop (input : list byte) : option (Z * Z) :=
  match candidateDecodeItem input with
  | candidateSuccess isList h p =>
      if (h + p <=? accessListSailSourceLimit) && isList
      then alSailEntries (alWindow input h p) else None
  | candidateError => None
  end.

(* A Sail AccessListDecode run against a model: the state is unchanged;
   Some (addresses, slots) is Success with these counts, None is Reject. *)
Definition alDecodeIs {addressBound slotBound : Z}
    (result : SailOutcome (ALT.AccessListDecode addressBound slotBound) * ALT.regstate)
    (rs : ALT.regstate) (model : option (Z * Z)) : Prop :=
  snd result = rs /\
  match model, fst result with
  | Some (addresses, slots), Success decoded =>
      ALT.AccessListDecode_address_count decoded = addresses /\
      ALT.AccessListDecode_slot_count decoded = slots
  | None, Reject RlpDecode => True
  | _, _ => False
  end.

(* The keys walk adds its count to the slots of the later entries. *)
Definition alKeysModel {addressBound slotBound : Z}
    (tail : ALT.AccessListDecode addressBound slotBound) (keys : list byte) : option (Z * Z) :=
  option_map (fun count =>
    (ALT.AccessListDecode_address_count tail, ALT.AccessListDecode_slot_count tail + count))
    (alSailKeys keys).

Definition alFieldOk {base full content : Z} (field : ALT.RlpFieldRef base full content)
    (isList : bool) : Prop :=
  ALT.RlpFieldRef_is_list field = isList /\
  ALT.RlpFieldRef_content_len field = content /\
  ALT.StatelessInputSliceFields_len (ALT.RlpFieldRef_source field) = full.

(* ---- candidate views ---- *)

Definition alCandidateItem (r : list byte) : option (bool * Z * Z) :=
  match candidateDecodeItem r with
  | candidateSuccess isList h p => Some (isList, h, p)
  | candidateError => None
  end.

Definition alCandKeys (fuel : nat) (keys : list byte) : option Z :=
  option_map (fun found => Z.of_nat (List.length found)) (snd (accessListKeysWalk fuel keys)).

Definition alCandEntry (entry : list byte) : option Z :=
  option_map (fun value => Z.of_nat (List.length (entryKeys value))) (snd (accessListEntry entry)).

Definition alCandEntries (fuel : nat) (entries : list byte) : option (Z * Z) :=
  option_map (fun values => (Z.of_nat (List.length values), accessListKeyCount values))
    (snd (accessListEntriesWalk fuel entries)).

Definition alCandTop (input : list byte) : option (Z * Z) :=
  match candidateAccessList input with
  | accessListAccepted entries _ =>
      Some (Z.of_nat (List.length entries), accessListKeyCount entries)
  | accessListRejected _ => None
  end.

(* ---- domain and trigger hits per reached call ---- *)

(* headerFits as a boolean: the body of accessListHeadersFitb. *)
Definition alHeaderFitsb (bytes : list byte) : bool :=
  match bytes with
  | nil => true
  | prefix :: rest =>
      let width := longLengthWidth (bv_unsigned prefix) in
      (width =? 0) || (Z.of_nat (List.length rest) <? width) ||
      (1 + width + bigEndian (firstn (Z.to_nat width) rest) <? word64Modulus)
  end.

Definition alCallsFitb (calls : list AccessListCall) : bool :=
  forallb (fun call => alHeaderFitsb (snd call)) calls.

Definition alTopDomainb (input : list byte) : bool :=
  accessListHeadersFitb input &&
  match candidateDecodeItem input with
  | candidateSuccess _ h p => h + p <=? accessListSailSourceLimit
  | candidateError => true
  end.

(* The per-call bodies of accessListAddressLengthb (D1),
   accessListKeyLengthb (D2) and accessListEntryTrailingb (D3). *)
Definition alAddressHitb (call : AccessListCall) : bool :=
  accessListStringAtb accessListAddressCall
    (fun length => negb (length =? accessListAddressBytes) && (length <=? 32)) call.

Definition alKeyHitb (call : AccessListCall) : bool :=
  accessListStringAtb accessListKeyCall (fun length => length <? accessListKeyBytes) call.

Definition alTrailingHitb (call : AccessListCall) : bool :=
  (fst call =? accessListKeysCall) &&
  match candidateDecodeItem (snd call) with
  | candidateSuccess true headerLength payloadLength =>
      negb (Nat.eqb (List.length (itemRest (snd call) headerLength payloadLength)) 0)
  | candidateSuccess false _ _ | candidateError => false
  end.

Definition alHitb (call : AccessListCall) : bool :=
  alAddressHitb call || alKeyHitb call || alTrailingHitb call.

(* ---- statements, in dependency order ---- *)

(* alRunBind [M]: runAccessListPrompt through bind (induction on the action). Uses: none (leaf). *)
Definition alRunBind_statement : Prop :=
  forall (A B : Type) (action : ALT.M A) (next : A -> ALT.M B) (rs : ALT.regstate) (allow : bool),
    runAccessListPrompt (SailStdpp.Prompt_monad.bind action next) rs allow =
    match runAccessListPrompt action rs allow with
    | (Success value, rs') => runAccessListPrompt (next value) rs' allow
    | (Reject error, rs') => (Reject error, rs')
    | (UnsupportedOrInternalFailure message, rs') => (UnsupportedOrInternalFailure message, rs')
    end.

(* alRunBindAssoc [M]: bind associativity under the runner. Uses: alRunBind. *)
Definition alRunBindAssoc_statement : Prop :=
  forall (A B C : Type) (action : ALT.M A) (next : A -> ALT.M B) (last : B -> ALT.M C)
      (rs : ALT.regstate) (allow : bool),
    runAccessListPrompt
      (SailStdpp.Prompt_monad.bind (SailStdpp.Prompt_monad.bind action next) last) rs allow =
    runAccessListPrompt
      (SailStdpp.Prompt_monad.bind action
         (fun value => SailStdpp.Prompt_monad.bind (next value) last)) rs allow.

(* alRunAssertTrue [M]: a true assert_exp' succeeds. Uses: none (leaf). *)
Definition alRunAssertTrue_statement : Prop :=
  forall (condition : bool) (message : string) (Htrue : condition = true)
      (rs : ALT.regstate) (allow : bool),
    runAccessListPrompt (SailStdpp.Prompt_monad.assert_exp' condition message) rs allow =
      (Success Htrue, rs).

(* alRunFatal [M]: fatal_error RlpDecode is Reject RlpDecode. Uses: none (leaf). *)
Definition alRunFatal_statement : Prop :=
  forall (A : Type) (rs : ALT.regstate),
    runAccessListPrompt (@ALS.fatal_error A ALT.RlpDecode) rs true = (Reject RlpDecode, rs).

(* alRunShimByte [M]: shim_byte_at reads nth_error. Uses: none (leaf). *)
Definition alRunShimByte_statement : Prop :=
  forall (bytes : list byte) (offset : Z) (value : byte) (rs : ALT.regstate) (allow : bool),
    0 <= offset -> nth_error bytes (Z.to_nat offset) = Some value ->
    runAccessListPrompt (ALS.shim_byte_at bytes offset) rs allow = (Success value, rs).

(* alShimInputLength [M]: shim_input_length is the list length. Uses: none (leaf). *)
Definition alShimInputLength_statement : Prop :=
  forall bytes : list byte, ALS.shim_input_length bytes = Z.of_nat (List.length bytes).

(* alRunInit [M]: model init then input install: a state holding the bytes. Uses: alRunBind. *)
Definition alRunInit_statement : Prop :=
  forall bytes : list byte,
    exists rs : ALT.regstate,
      alRegs rs bytes /\
      forall (A : Type) (action : ALT.M A),
        runAccessListPrompt
          (SailStdpp.Prompt_monad.bind0 (initializedAccessListInput bytes) action)
          ALT.init_regstate true =
        runAccessListPrompt action rs true.

(* alWindowSuffix [L]: window of a cursor advance is skipn of the window. Uses: none (leaf). *)
Definition alWindowSuffix_statement : Prop :=
  forall (bytes : list byte) (base len advance : Z),
    alSliceIn bytes base len -> 0 <= advance <= len ->
    alWindow bytes (base + advance) (len - advance) =
      skipn (Z.to_nat advance) (alWindow bytes base len).

(* alWindowSub [L]: window of a sub-slice is firstn/skipn of the window. Uses: none (leaf). *)
Definition alWindowSub_statement : Prop :=
  forall (bytes : list byte) (base len offset size : Z),
    alSliceIn bytes base len -> 0 <= offset -> 0 <= size -> offset + size <= len ->
    alWindow bytes (base + offset) size =
      firstn (Z.to_nat size) (skipn (Z.to_nat offset) (alWindow bytes base len)).

(* alBigEndianNonneg [L]: bigEndian is non-negative. Uses: none (leaf). *)
Definition alBigEndianNonneg_statement : Prop :=
  forall bytes : list byte, 0 <= bigEndian bytes.

(* alDomainReflect [P]: the Prop domain gives the boolean domain. Uses: none (leaf). *)
Definition alDomainReflect_statement : Prop :=
  forall input : list byte, txAccessListDomain input -> alTopDomainb input = true.

(* alSailItemShort [P]: Sail's item header equals candidateDecodeItem for a short prefix (below 184, or 192 to 247). Uses: none (leaf). *)
Definition alSailItemShort_statement : Prop :=
  forall (prefix : byte) (rest : list byte),
    bv_unsigned prefix < 184 \/ 192 <= bv_unsigned prefix < 248 ->
    alSailItem (prefix :: rest) = alCandidateItem (prefix :: rest).

(* alSailItemLong [P]: Sail's item header equals candidateDecodeItem for a long prefix (184 to 191, or 248 up) when the length does not wrap. Uses: alBigEndianNonneg. *)
Definition alSailItemLong_statement : Prop :=
  forall (prefix : byte) (rest : list byte),
    184 <= bv_unsigned prefix < 192 \/ 248 <= bv_unsigned prefix ->
    alHeaderFitsb (prefix :: rest) = true ->
    alSailItem (prefix :: rest) = alCandidateItem (prefix :: rest).

(* alSailItemCandidate [P]: Sail's item header equals candidateDecodeItem when the long length does not wrap. Uses: alSailItemShort, alSailItemLong. *)
Definition alSailItemCandidate_statement : Prop :=
  forall r : list byte, alHeaderFitsb r = true -> alSailItem r = alCandidateItem r.

(* alSailItemBounds [P]: a decoded Sail item is non-empty and inside the input. Uses: none (leaf). *)
Definition alSailItemBounds_statement : Prop :=
  forall (r : list byte) (isList : bool) (h p : Z),
    alSailItem r = Some (isList, h, p) ->
    0 <= h /\ 0 <= p /\ 0 < h + p /\ h + p <= Z.of_nat (List.length r).

(* alSailKeysFuelEnough [P]: alSailKeysFuel is fuel-independent above the length. Uses: alSailItemBounds. *)
Definition alSailKeysFuelEnough_statement : Prop :=
  forall (fuel : nat) (keys : list byte),
    (List.length keys <= fuel)%nat -> alSailKeysFuel fuel keys = alSailKeys keys.

(* alSailEntriesFuelEnough [P]: alSailEntriesFuel is fuel-independent above the length. Uses: alSailItemBounds. *)
Definition alSailEntriesFuelEnough_statement : Prop :=
  forall (fuel : nat) (entries : list byte),
    (List.length entries <= fuel)%nat -> alSailEntriesFuel fuel entries = alSailEntries entries.

(* alSailKeysCons [P]: alSailKeys of a non-empty list: one key item, then alSailKeys of the rest. Uses: alSailItemBounds, alSailKeysFuelEnough. *)
Definition alSailKeysCons_statement : Prop :=
  forall keys : list byte,
    keys <> nil ->
    alSailKeys keys =
      match alSailItem keys with
      | Some (false, h, p) =>
          if p <=? 32 then option_map (Z.add 1) (alSailKeys (alSkip keys h p)) else None
      | _ => None
      end.

(* alSailEntriesCons [P]: alSailEntries of a non-empty list: one entry item, then alSailEntries of the rest. Uses: alSailItemBounds, alSailEntriesFuelEnough. *)
Definition alSailEntriesCons_statement : Prop :=
  forall entries : list byte,
    entries <> nil ->
    alSailEntries entries =
      match alSailItem entries with
      | Some (true, h, p) =>
          match alSailEntry (alWindow entries h p), alSailEntries (alSkip entries h p) with
          | Some keys, Some (addresses, slots) => Some (addresses + 1, slots + keys)
          | _, _ => None
          end
      | _ => None
      end.

(* alCandItemNoWrap [P]: a decoded candidate item whose header fits does not wrap 2^64. Uses: none (leaf). *)
Definition alCandItemNoWrap_statement : Prop :=
  forall (r : list byte) (isList : bool) (h p : Z),
    alHeaderFitsb r = true -> candidateDecodeItem r = candidateSuccess isList h p ->
    h + p < word64Modulus.

(* alKeysAgree [P]: keys walk: Sail count = candidate count, or a D2 key-length hit. Uses: alSailItemCandidate, alSailItemBounds, alSailKeysFuelEnough, alCandItemNoWrap. *)
Definition alKeysAgree_statement : Prop :=
  forall (fuel : nat) (keys : list byte),
    (List.length keys <= fuel)%nat ->
    alCallsFitb (fst (accessListKeysWalk fuel keys)) = true ->
    alSailKeys keys = alCandKeys fuel keys \/
    existsb alKeyHitb (fst (accessListKeysWalk fuel keys)) = true.

(* alEntryAgree [P]: one entry: Sail key count = candidate key count, or a D1/D2/D3 hit. Uses: alSailItemCandidate, alSailItemBounds, alKeysAgree, alCandItemNoWrap. *)
Definition alEntryAgree_statement : Prop :=
  forall entry : list byte,
    alCallsFitb (fst (accessListEntry entry)) = true ->
    alSailEntry entry = alCandEntry entry \/ existsb alHitb (fst (accessListEntry entry)) = true.

(* alEntriesAgree [P]: entries walk: Sail counts = candidate counts, or a hit. Uses: alSailItemCandidate, alSailItemBounds, alSailEntriesFuelEnough, alEntryAgree, alCandItemNoWrap. *)
Definition alEntriesAgree_statement : Prop :=
  forall (fuel : nat) (entries : list byte),
    (List.length entries <= fuel)%nat ->
    alCallsFitb (fst (accessListEntriesWalk fuel entries)) = true ->
    alSailEntries entries = alCandEntries fuel entries \/
    existsb alHitb (fst (accessListEntriesWalk fuel entries)) = true.

(* alHitsTriggers [P]: per-call hits are the three proposed triggers. Uses: none (leaf). *)
Definition alHitsTriggers_statement : Prop :=
  forall input : list byte,
    existsb alHitb (accessListCalls input) =
    existsb (fun triggered => triggered) (accessListProposedTriggers input).

(* alTopAgree [P]: whole input: Sail model = candidate model, or a hit. Uses: alEntriesAgree. *)
Definition alTopAgree_statement : Prop :=
  forall input : list byte,
    alTopDomainb input = true ->
    alSailTop input = alCandTop input \/ existsb alHitb (accessListCalls input) = true.

(* alSliceByte [W]: stateless_input_slice_byte inside the slice. Uses: alRunBind, alRunAssertTrue, alRunShimByte, alShimInputLength. *)
Definition alSliceByte_statement : Prop :=
  forall (bytes : list byte) (rs : ALT.regstate) (base len : Z) (s : ALT.StatelessInputSliceFields base len) (off : Z),
    alRegs rs bytes -> alSliceIn bytes base len -> 0 <= off < len ->
    runAccessListPrompt (ALS.stateless_input_slice_byte s off) rs true =
      (Success (nth (Z.to_nat off) (alWindow bytes base len) (BV 8 0)), rs).

(* alRecWidth [W]: _rec_rlp_uint64_width is bigEndian of the first n window bytes (induction on n). Uses: alRunBind, alRunAssertTrue, alSliceByte. *)
Definition alRecWidth_statement : Prop :=
  forall (bytes : list byte) (rs : ALT.regstate) (base len : Z) (s : ALT.StatelessInputSliceFields base len) (n : nat) (fuel : Z)
      (acc : Acc (Zwf 0) fuel),
    alRegs rs bytes -> alSliceIn bytes base len -> Z.of_nat n <= len -> Z.of_nat n <= fuel ->
    runAccessListPrompt (ALS._rec_rlp_uint64_width s (Z.of_nat n) fuel acc) rs true =
      (Success (bigEndian (firstn n (alWindow bytes base len))), rs).

(* alRefHdr [W]: rlp_ref_hdr is the pure header alSailHdr of the window. Uses: alRunBind, alRunBindAssoc, alRunFatal, alSliceByte, alRecWidth, alWindowSub. *)
Definition alRefHdr_statement : Prop :=
  forall (bytes : list byte) (rs : ALT.regstate) (base len : Z) (s : ALT.StatelessInputSliceFields base len),
    alRegs rs bytes -> alSliceIn bytes base len -> ALT.StatelessInputSliceFields_len s = len ->
    runAccessListPrompt (ALS.rlp_ref_hdr s) rs true =
      (alHdrOutcome (alSailHdr (alWindow bytes base len)), rs).

(* alDecodeItem [W]: rlp_decode_item is the pure item alSailItem of the window. Uses: alRunBind, alRunBindAssoc, alRunFatal, alRefHdr, alBigEndianNonneg. *)
Definition alDecodeItem_statement : Prop :=
  forall (bytes : list byte) (rs : ALT.regstate) (base len : Z) (s : ALT.StatelessInputSliceFields base len),
    alRegs rs bytes -> alSliceIn bytes base len -> ALT.StatelessInputSliceFields_len s = len ->
    match alSailItem (alWindow bytes base len) with
    | None => runAccessListPrompt (ALS.rlp_decode_item s) rs true = (Reject RlpDecode, rs)
    | Some (isList, h, p) =>
        exists field : ALT.RlpFieldRef base (h + p) p,
          runAccessListPrompt (ALS.rlp_decode_item s) rs true =
            (Success (@existT Z (fun full => {content : Z & ALT.RlpFieldRef base full content})
               (h + p) (@existT Z (fun content => ALT.RlpFieldRef base (h + p) content) p field)), rs) /\
          alFieldOk field isList
    end.

(* alDecodeList [W]: rlp_decode_list: the content sub-slice of a list, else Reject. Uses: alRunFatal. *)
Definition alDecodeList_statement : Prop :=
  forall (base full content : Z) (f : ALT.RlpFieldRef base full content) (rs : ALT.regstate),
    runAccessListPrompt (ALS.rlp_decode_list f) rs true =
      ((if ALT.RlpFieldRef_is_list f
        then Success (ALS.stateless_input_sub_slice (ALT.RlpFieldRef_source f) (full - content) content)
        else Reject RlpDecode), rs).

(* alExpectEnd [W]: rlp_cursor_expect_end: success iff the cursor is empty. Uses: alRunFatal. *)
Definition alExpectEnd_statement : Prop :=
  forall (base len : Z) (s : ALT.StatelessInputSliceFields base len) (rs : ALT.regstate),
    runAccessListPrompt (ALS.rlp_cursor_expect_end s) rs true =
      ((if len =? 0 then Success tt else Reject RlpDecode), rs).

(* alRecShimLoad [W]: _rec_shim_load_n succeeds without a failed assert (induction on remaining). Uses: alRunBind, alRunAssertTrue, alRunShimByte. *)
Definition alRecShimLoad_statement : Prop :=
  forall (bytes : list byte) (rs : ALT.regstate) (base len : Z) (s : ALT.StatelessInputSliceFields base len)
      (off remaining value fuel : Z) (acc : Acc (Zwf 0) fuel),
    alRegs rs bytes -> alSliceIn bytes base len -> 0 <= off -> 0 <= remaining <= fuel ->
    exists result : Z,
      runAccessListPrompt (ALS._rec_shim_load_n s off remaining value fuel acc) rs true =
        (Success result, rs).

(* alSliceLoadN [W]: stateless_input_slice_load_n succeeds. Uses: alRunBind, alRunAssertTrue, alShimInputLength, alRecShimLoad. *)
Definition alSliceLoadN_statement : Prop :=
  forall (bytes : list byte) (rs : ALT.regstate) (base len : Z) (s : ALT.StatelessInputSliceFields base len) (off n : Z),
    alRegs rs bytes -> alSliceIn bytes base len -> 0 <= off -> 0 <= n <= 32 ->
    exists w : ALT.word,
      runAccessListPrompt (ALS.stateless_input_slice_load_n s off n) rs true = (Success w, rs).

(* alDecodeWord [W]: rlp_decode_word rejects exactly lists and strings above 32 bytes. Uses: alRunBind, alRunFatal, alSliceLoadN. *)
Definition alDecodeWord_statement : Prop :=
  forall (bytes : list byte) (rs : ALT.regstate) (base full content : Z)
      (f : ALT.RlpFieldRef base full content),
    alRegs rs bytes -> alSliceIn bytes base full -> 0 <= content <= full ->
    if ALT.RlpFieldRef_is_list f || (32 <? content)
    then runAccessListPrompt (ALS.rlp_decode_word f) rs true = (Reject RlpDecode, rs)
    else exists w : ALT.word, runAccessListPrompt (ALS.rlp_decode_word f) rs true = (Success w, rs).

(* alKeysStep [W]: one unfolding of _rec_decode_access_list_keys, the recursive call given. Uses: alRunBind, alRunAssertTrue, alDecodeItem, alDecodeWord, alWindowSuffix, alSailItemBounds, alSailKeysCons. *)
Definition alKeysStep_statement : Prop :=
  forall (bytes : list byte) (rs : ALT.regstate) (base len : Z) (s : ALT.StatelessInputSliceFields base len) (addr : ALT.address)
      (addressBound slotBound : Z) (tail : ALT.AccessListDecode addressBound slotBound)
      (fuel : Z) (acc : Acc (Zwf 0) fuel),
    alRegs rs bytes -> alSliceIn bytes base len -> ALT.StatelessInputSliceFields_len s = len ->
    0 < len -> len <= fuel ->
    (forall (base' len' : Z) (s' : ALT.StatelessInputSliceFields base' len')
        (acc' : Acc (Zwf 0) (fuel - 1)),
       alSliceIn bytes base' len' -> ALT.StatelessInputSliceFields_len s' = len' -> len' < len ->
       alDecodeIs
         (runAccessListPrompt (ALS._rec_decode_access_list_keys s' addr tail (fuel - 1) acc') rs true)
         rs (alKeysModel tail (alWindow bytes base' len'))) ->
    alDecodeIs (runAccessListPrompt (ALS._rec_decode_access_list_keys s addr tail fuel acc) rs true)
      rs (alKeysModel tail (alWindow bytes base len)).

(* alKeysRec [W]: _rec_decode_access_list_keys is alSailKeys (strong induction on len). Uses: alRunBind, alRunAssertTrue, alKeysStep. *)
Definition alKeysRec_statement : Prop :=
  forall (bytes : list byte) (rs : ALT.regstate) (base len : Z) (s : ALT.StatelessInputSliceFields base len) (addr : ALT.address)
      (addressBound slotBound : Z) (tail : ALT.AccessListDecode addressBound slotBound)
      (fuel : Z) (acc : Acc (Zwf 0) fuel),
    alRegs rs bytes -> alSliceIn bytes base len -> ALT.StatelessInputSliceFields_len s = len ->
    len <= fuel ->
    alDecodeIs (runAccessListPrompt (ALS._rec_decode_access_list_keys s addr tail fuel acc) rs true)
      rs (alKeysModel tail (alWindow bytes base len)).

(* alEntriesStepNotList [W]: one unfolding of _rec_decode_access_list_entries when the first item is not a list: Reject. Uses: alRunBind, alRunAssertTrue, alDecodeItem, alDecodeList. *)
Definition alEntriesStepNotList_statement : Prop :=
  forall (bytes : list byte) (rs : ALT.regstate) (base len : Z) (s : ALT.StatelessInputSliceFields base len)
      (fuel : Z) (acc : Acc (Zwf 0) fuel),
    alRegs rs bytes -> alSliceIn bytes base len -> ALT.StatelessInputSliceFields_len s = len ->
    0 < len -> len <= fuel ->
    (forall h p : Z, alSailItem (alWindow bytes base len) <> Some (true, h, p)) ->
    alDecodeIs (runAccessListPrompt (ALS._rec_decode_access_list_entries s fuel acc) rs true) rs None.

(* alEntriesStepList [W]: one unfolding of _rec_decode_access_list_entries on a list item, the recursive call given. Uses: alRunBind, alRunAssertTrue, alDecodeItem, alDecodeList, alExpectEnd, alDecodeWord, alKeysRec, alWindowSuffix, alWindowSub, alSailItemBounds. *)
Definition alEntriesStepList_statement : Prop :=
  forall (bytes : list byte) (rs : ALT.regstate) (base len : Z) (s : ALT.StatelessInputSliceFields base len)
      (fuel : Z) (acc : Acc (Zwf 0) fuel) (h p : Z),
    alRegs rs bytes -> alSliceIn bytes base len -> ALT.StatelessInputSliceFields_len s = len ->
    0 < len -> len <= fuel ->
    alSailItem (alWindow bytes base len) = Some (true, h, p) ->
    (forall (base' len' : Z) (s' : ALT.StatelessInputSliceFields base' len')
        (acc' : Acc (Zwf 0) (fuel - 1)),
       alSliceIn bytes base' len' -> ALT.StatelessInputSliceFields_len s' = len' -> len' < len ->
       alDecodeIs (runAccessListPrompt (ALS._rec_decode_access_list_entries s' (fuel - 1) acc') rs true)
         rs (alSailEntries (alWindow bytes base' len'))) ->
    alDecodeIs (runAccessListPrompt (ALS._rec_decode_access_list_entries s fuel acc) rs true) rs
      (match alSailEntry (alWindow bytes (base + h) p),
             alSailEntries (alWindow bytes (base + (h + p)) (len - (h + p))) with
       | Some keys, Some (addresses, slots) => Some (addresses + 1, slots + keys)
       | _, _ => None
       end).

(* alEntriesStep [W]: one unfolding of _rec_decode_access_list_entries, the recursive call given. Uses: alEntriesStepNotList, alEntriesStepList, alSailEntriesCons, alSailItemBounds, alWindowSub, alWindowSuffix. *)
Definition alEntriesStep_statement : Prop :=
  forall (bytes : list byte) (rs : ALT.regstate) (base len : Z) (s : ALT.StatelessInputSliceFields base len)
      (fuel : Z) (acc : Acc (Zwf 0) fuel),
    alRegs rs bytes -> alSliceIn bytes base len -> ALT.StatelessInputSliceFields_len s = len ->
    0 < len -> len <= fuel ->
    (forall (base' len' : Z) (s' : ALT.StatelessInputSliceFields base' len')
        (acc' : Acc (Zwf 0) (fuel - 1)),
       alSliceIn bytes base' len' -> ALT.StatelessInputSliceFields_len s' = len' -> len' < len ->
       alDecodeIs (runAccessListPrompt (ALS._rec_decode_access_list_entries s' (fuel - 1) acc') rs true)
         rs (alSailEntries (alWindow bytes base' len'))) ->
    alDecodeIs (runAccessListPrompt (ALS._rec_decode_access_list_entries s fuel acc) rs true)
      rs (alSailEntries (alWindow bytes base len)).

(* alEntriesRec [W]: _rec_decode_access_list_entries is alSailEntries (strong induction on len). Uses: alRunBind, alRunAssertTrue, alEntriesStep. *)
Definition alEntriesRec_statement : Prop :=
  forall (bytes : list byte) (rs : ALT.regstate) (base len : Z) (s : ALT.StatelessInputSliceFields base len)
      (fuel : Z) (acc : Acc (Zwf 0) fuel),
    alRegs rs bytes -> alSliceIn bytes base len -> ALT.StatelessInputSliceFields_len s = len ->
    len <= fuel ->
    alDecodeIs (runAccessListPrompt (ALS._rec_decode_access_list_entries s fuel acc) rs true)
      rs (alSailEntries (alWindow bytes base len)).

(* alDecodeAccessList [W]: decode_access_list on a field: 2^30 guard, list check, entries walk, counts and span. Uses: alRunBind, alRunFatal, alDecodeList, alEntriesRec, alWindowSub. *)
Definition alDecodeAccessList_statement : Prop :=
  forall (bytes : list byte) (rs : ALT.regstate) (base len content : Z)
      (f : ALT.RlpFieldRef base len content),
    alRegs rs bytes -> alSliceIn bytes base len -> 0 <= content <= len ->
    ALT.StatelessInputSliceFields_len (ALT.RlpFieldRef_source f) = len ->
    match (if (len <=? accessListSailSourceLimit) && ALT.RlpFieldRef_is_list f
           then alSailEntries (alWindow bytes (base + (len - content)) content) else None) with
    | Some (addresses, slots) =>
        exists ref : ALT.AccessListRef,
          runAccessListPrompt (ALS.decode_access_list f) rs true = (Success ref, rs) /\
          accessListCounts (Success ref) = Some (addresses, slots) /\
          accessListEncodedSpan ref = (base + (len - content), content)
    | None => runAccessListPrompt (ALS.decode_access_list f) rs true = (Reject RlpDecode, rs)
    end.

(* alRunDecodeAccessList [W]: runDecodeAccessList on the first item's field is the pure Sail model. Uses: alRunInit, alShimInputLength, alDecodeAccessList. *)
Definition alRunDecodeAccessList_statement : Prop :=
  forall (bytes : list byte) (isList : bool) (h p : Z),
    0 <= h -> 0 <= p -> h + p <= Z.of_nat (List.length bytes) -> h + p <= 2 ^ 32 - 1 ->
    match (if (h + p <=? accessListSailSourceLimit) && isList
           then alSailEntries (alWindow bytes h p) else None) with
    | Some (addresses, slots) =>
        exists ref : ALT.AccessListRef,
          runDecodeAccessList bytes (accessListSailField isList h p) = Success ref /\
          accessListCounts (Success ref) = Some (addresses, slots) /\
          accessListEncodedSpan ref = (h, p)
    | None => runDecodeAccessList bytes (accessListSailField isList h p) = Reject RlpDecode
    end.

(* txAccessListSailAgreesModuloProposed [C]: TOP: Sail agrees with the candidate, or a proposed trigger D1/D2/D3 holds. Uses: alRunDecodeAccessList, alDomainReflect, alSailItemCandidate, alSailItemBounds, alHitsTriggers, alTopAgree. *)
Definition txAccessListSailAgreesModuloProposed_statement : Prop :=
  forall input : list byte,
    txAccessListDomain input ->
    txAccessListSailAgrees input \/
    existsb (fun triggered => triggered) (accessListProposedTriggers input) = true.
