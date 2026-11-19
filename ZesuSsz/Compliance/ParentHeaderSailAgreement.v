From Coq Require Import Bool List ZArith Lia.
From stdpp Require Import bitvector.definitions.
Require Import SailStdpp.MachineWord.
Require Import EvmSailRlp.evm_rlp_types EvmSailRlp.evm_rlp.
Require Import ZesuSsz.Compliance.KnownBugs.
Require Import ZesuSsz.Contracts.RlpDecodeItem.
Require Import ZesuSsz.Contracts.ParentHeader.
Require Import ZesuSsz.Contracts.Candidates.ParentHeaderDomain.
Require Import ZesuSsz.Contracts.Candidates.ParentHeaderCandidate.
Require Import ZesuSsz.Contracts.ParentHeaderBugTriggers.
Require Import ZesuSsz.Compliance.RlpInputBounds.
Require Import ZesuSsz.Compliance.SailRun.
Require Import ZesuSsz.Compliance.ProjectionParentHeader.
Require Import ZesuSsz.Contracts.ParentHeaderRung2.

Import ListNotations.
Open Scope Z_scope.

(* Plan step 2.4, M2: candidateParentHeader against Sail's
   decode_parent_header_fields (generated/evm-sail-coq/rlp/evm_rlp.v,
   _rec_decode_parent_header_fields; pinned stateless_input.sail).

   Structure of the argument:
   1. sailPureParentHeader is a pure model of sailParentHeaderRun on the
      whole input (rlp_node_cursor, then the field loop). That the monadic
      run computes this model is SailParentHeaderModel (the Sail evaluation
      step; not proved here).
   2. fieldDivergentb lists, per reached field, every item shape on which
      the candidate's step and Sail's step can disagree; walkNoDivergence
      adds a missing required field and a malformed item after field 18,
      parentHeaderNoDivergence the outer item. KnownBugTriggersCoverDivergences
      says the KnownBug triggers exclude all of them. With the drafted
      triggers it is false: the scratch module
      _build/agents/rebuild/2.4m2/DivergenceWitnesses.v computes inputs on
      which no trigger fires and parentHeaderNoDivergence is false.
   3. One step lemma per field kind (FieldStepAgrees): outside
      fieldDivergentb the candidate's step and Sail's step agree. All 19
      are proved below.
   4. candidateParentHeader_sail_from_steps composes 1 to 3 by induction on
      parentHeaderFieldSchedule.
   Owner: contract fact (statement of the M2 obligation and its pieces). *)

(* Sail's default execution profile (schema 0x15 falls through to
   Amsterdam in schema_protocol_profile): blob schedule maximum 21, excess
   blob gas limit 256 * 11684671 + (21 - 14) * 2^17
   (compute_profile_excess_blob_gas_limit). The run installs it in
   sail_model_init (initializedInput). *)
Notation sailBlobMax := 21 (only parsing).
Notation sailExcessBlobGasLimit := (256 * 11684671 + (21 - 14) * 2 ^ 17) (only parsing).

Record SailParentValues := {
  sailBaseFee : option Z;
  sailBlobGasUsed : option Z;
  sailExcessBlobGas : option Z;
}.

Definition sailNoValues : SailParentValues :=
  {| sailBaseFee := None; sailBlobGasUsed := None; sailExcessBlobGas := None |}.

(* rlp_decode_item on a cursor holding exactly [r]: the same header as
   candidateDecodeItem, without the 2^64 wrap of the binary. *)
Definition sailDecodeItem (r : list byte) : candidateItem :=
  match candidateDecodeItem r with
  | candidateSuccess isList headerLength payloadLength =>
      if headerLength + payloadLength <=? Z.of_nat (List.length r)
      then candidateSuccess isList headerLength payloadLength
      else candidateError
  | candidateError => candidateError
  end.

Definition itemPayload (r : list byte) (headerLength payloadLength : Z)
    : list byte :=
  firstn (Z.to_nat payloadLength) (skipn (Z.to_nat headerLength) r).

(* rlp_item_uint_canonical (rlp_ref_bytes_canonical, rlp_ref_framing_canonical
   and the leading-zero check) for an item of at most 55 payload bytes.
   Above 55 Sail's integer decoders reject anyway (32 and 8 byte limits). *)
Definition sailShortUintCanonical (r : list byte) (isList : bool)
    (headerLength payloadLength : Z) : bool :=
  negb isList && (payloadLength <=? 55) &&
  match r, itemPayload r headerLength payloadLength with
  | [], _ => false
  | first :: _, [] =>
      (payloadLength =? 0) && (headerLength =? 1) && (bv_unsigned first =? 128)
  | first :: _, lead :: _ =>
      negb (payloadLength =? 0) && negb (bv_unsigned lead =? 0) &&
      (if (payloadLength =? 1) && (bv_unsigned lead <? 128)
       then headerLength =? 0
       else (headerLength =? 1) && (bv_unsigned first =? 128 + payloadLength))
  end.

(* The body of _rec_decode_parent_header_fields after rlp_decode_item. *)
Definition sailFieldStep (index : nat) (r : list byte) (isList : bool)
    (headerLength payloadLength : Z) (acc : SailParentValues)
    : option SailParentValues :=
  let value := bigEndian (itemPayload r headerLength payloadLength) in
  let canonical := sailShortUintCanonical r isList headerLength payloadLength in
  if (index =? 0)%nat || (index =? 3)%nat then
    if isList || (32 <? payloadLength) then None else Some acc
  else if (index =? 15)%nat then
    if canonical && (payloadLength <=? 32)
    then Some {| sailBaseFee := Some value;
                 sailBlobGasUsed := sailBlobGasUsed acc;
                 sailExcessBlobGas := sailExcessBlobGas acc |}
    else None
  else if (index =? 17)%nat then
    if canonical && (payloadLength <=? 8) &&
       (value / 2 ^ 17 <=? sailBlobMax) && (value =? 2 ^ 17 * (value / 2 ^ 17))
    then Some {| sailBaseFee := sailBaseFee acc;
                 sailBlobGasUsed := Some value;
                 sailExcessBlobGas := sailExcessBlobGas acc |}
    else None
  else if (index =? 18)%nat then
    if canonical && (payloadLength <=? 8) && (value <=? sailExcessBlobGasLimit)
    then Some {| sailBaseFee := sailBaseFee acc;
                 sailBlobGasUsed := sailBlobGasUsed acc;
                 sailExcessBlobGas := Some value |}
    else None
  else Some acc.

Definition sailStep (index : nat) (r : list byte) (acc : SailParentValues)
    : option (list byte * SailParentValues) :=
  match sailDecodeItem r with
  | candidateError => None
  | candidateSuccess isList headerLength payloadLength =>
      match sailFieldStep index r isList headerLength payloadLength acc with
      | Some acc' => Some (skipn (Z.to_nat (headerLength + payloadLength)) r, acc')
      | None => None
      end
  end.

(* Field index 19 (the cursor saturates there): every further item is
   decoded by rlp_decode_item and discarded. *)
Fixpoint sailSkipItems (fuel : nat) (r : list byte) : bool :=
  match r with
  | [] => true
  | _ :: _ =>
      match fuel with
      | O => false
      | S fuel' =>
          match sailDecodeItem r with
          | candidateError => false
          | candidateSuccess _ headerLength payloadLength =>
              sailSkipItems fuel' (skipn (Z.to_nat (headerLength + payloadLength)) r)
          end
      end
  end.

Fixpoint sailFieldWalk (index count : nat) (r : list byte)
    (acc : SailParentValues) : option SailParentValues :=
  match count with
  | O => if sailSkipItems (List.length r) r then Some acc else None
  | S count' =>
      match r with
      | [] => Some acc
      | _ :: _ =>
          match sailStep index r acc with
          | None => None
          | Some (rest, acc') => sailFieldWalk (S index) count' rest acc'
          end
      end
  end.

(* rlp_node_cursor: rlp_single_ref (header and payload span the whole
   input) and rlp_decode_list, then the field loop from index 0. *)
Definition sailPureParentHeader (bytes : list byte) : option SailParentValues :=
  match candidateDecodeItem bytes with
  | candidateSuccess true headerLength payloadLength =>
      if headerLength + payloadLength =? Z.of_nat (List.length bytes)
      then sailFieldWalk 0 (List.length parentHeaderFieldSchedule)
             (itemPayload bytes headerLength payloadLength) sailNoValues
      else None
  | _ => None
  end.

Definition sailValuesOfFields (fields : ParentHeaderFields) : SailParentValues := {|
  sailBaseFee :=
    if ParentHeaderFields_have_base_fee fields
    then Some (word_value (ParentHeaderFields_base_fee fields)) else None;
  sailBlobGasUsed :=
    if ParentHeaderFields_have_blob_gas fields
    then Some (ParentHeaderFields_blob_gas_used fields) else None;
  sailExcessBlobGas :=
    if ParentHeaderFields_have_excess_blob_gas fields
    then Some (excess_blob_gas_value (ParentHeaderFields_excess_blob_gas fields))
    else None;
|}.

(* Step 1 (Sail evaluation, open): the monadic run computes the model. *)
Definition SailParentHeaderModel : Prop :=
  forall bytes : list byte,
    headerFits bytes -> Z.of_nat (List.length bytes) < 2 ^ 31 ->
    match sailPureParentHeader bytes with
    | None => sailParentHeaderRun bytes (parentHeaderSailNode bytes) = Reject RlpDecode
    | Some values =>
        exists fields,
          sailParentHeaderRun bytes (parentHeaderSailNode bytes) = Success fields /\
          sailValuesOfFields fields = values
    end.

(* The candidate's step on one reached field (the body of
   parentHeaderFieldWalk). *)
Inductive CandidateStep :=
| candidateStepReject
| candidateStepContinue (rest : list byte) (values : list Z).

Definition candidateFieldStep (kind : ParentHeaderFieldKind) (r : list byte)
    (values : list Z) : CandidateStep :=
  match candidateDecodeItem r with
  | candidateError => candidateStepReject
  | candidateSuccess isList headerLength payloadLength =>
      let rest := skipn
        (Z.to_nat ((headerLength + payloadLength) mod word64Modulus)) r in
      if parentHeaderFieldIsInteger kind then
        if isList || (8 <? payloadLength) then candidateStepReject
        else candidateStepContinue rest
          (values ++ [bigEndian (firstn (Z.to_nat payloadLength)
                       (skipn (Z.to_nat headerLength) r))])
      else candidateStepContinue rest values
  end.

(* Step 2: item shapes on which the two steps may disagree. *)
Definition candidateWrapb (r : list byte) : bool :=
  match candidateDecodeItem r with
  | candidateSuccess _ headerLength payloadLength =>
      Z.of_nat (List.length r) <? headerLength + payloadLength
  | candidateError => false
  end.

Definition fieldDivergentb (index : nat) (r : list byte) : bool :=
  candidateWrapb r ||
  match candidateDecodeItem r with
  | candidateError => false
  | candidateSuccess isList headerLength payloadLength =>
      let value := bigEndian (itemPayload r headerLength payloadLength) in
      let canonical := sailShortUintCanonical r isList headerLength payloadLength in
      if (index =? 0)%nat || (index =? 3)%nat then
        isList || (32 <? payloadLength)
      else if (9 <=? index)%nat && (index <=? 11)%nat then
        isList || (8 <? payloadLength)
      else if (index =? 15)%nat then
        negb isList &&
        ((8 <? payloadLength) && (payloadLength <=? 32) && canonical ||
         (payloadLength <=? 8) && negb canonical)
      else if (index =? 17)%nat then
        negb isList && (payloadLength <=? 8) &&
        negb (canonical && (value / 2 ^ 17 <=? sailBlobMax) &&
              (value =? 2 ^ 17 * (value / 2 ^ 17)))
      else if (index =? 18)%nat then
        negb isList && (payloadLength <=? 8) &&
        negb (canonical && (value <=? sailExcessBlobGasLimit))
      else false
  end.

Fixpoint walkNoDivergence (index : nat)
    (schedule : list (Z * ParentHeaderFieldKind)) (r : list byte)
    (values : list Z) : bool :=
  match schedule with
  | [] => sailSkipItems (List.length r) r
  | (_, kind) :: later =>
      match r with
      | [] => negb (parentHeaderFieldIsRequired kind)
      | _ :: _ =>
          negb (fieldDivergentb index r) &&
          match candidateFieldStep kind r values with
          | candidateStepReject => true
          | candidateStepContinue rest values' =>
              walkNoDivergence (S index) later rest values'
          end
      end
  end.

Definition parentHeaderNoDivergence (bytes : list byte) : bool :=
  match candidateDecodeItem bytes with
  | candidateSuccess true headerLength payloadLength =>
      if headerLength + payloadLength <=? Z.of_nat (List.length bytes)
      then (headerLength + payloadLength =? Z.of_nat (List.length bytes)) &&
           (0 <? payloadLength) &&
           walkNoDivergence 0 parentHeaderFieldSchedule
             (itemPayload bytes headerLength payloadLength) []
      else true
  | _ => true
  end.

(* Open: false for the drafted triggers (see DIVERGENCES.md of the lane). *)
Definition KnownBugTriggersCoverDivergences : Prop :=
  forall bytes : list byte,
    headerFits bytes -> Z.of_nat (List.length bytes) < 2 ^ 31 ->
    (forall bug, List.In bug knownBugs -> parentHeaderBugTrigger bug bytes = false) ->
    parentHeaderNoDivergence bytes = true.

(* Step 3: per-field agreement. *)
Definition intFieldsBefore (index : nat) : nat :=
  List.length (List.filter (fun entry => parentHeaderFieldIsInteger (snd entry))
    (firstn index parentHeaderFieldSchedule)).

Definition projectValues (values : list Z) : SailParentValues := {|
  sailBaseFee := nth_error values 3;
  sailBlobGasUsed := nth_error values 4;
  sailExcessBlobGas := nth_error values 5;
|}.

Definition sailValuesMatch (index : nat) (values : list Z)
    (acc : SailParentValues) : Prop :=
  acc = projectValues values /\
  List.length values = intFieldsBefore index /\
  Forall (fun value => 0 <= value < 2 ^ 64) values.

Definition FieldStepAgrees (index : nat) (kind : ParentHeaderFieldKind) : Prop :=
  forall r values acc,
    r <> [] -> Z.of_nat (List.length r) < 2 ^ 31 ->
    sailValuesMatch index values acc ->
    fieldDivergentb index r = false ->
    match candidateFieldStep kind r values with
    | candidateStepReject => sailStep index r acc = None
    | candidateStepContinue rest values' =>
        exists acc', sailStep index r acc = Some (rest, acc') /\
          sailValuesMatch (S index) values' acc'
    end.

(* Arithmetic facts. *)
Lemma digitFoldBound {A : Type} (digit : A -> Z) (bytes : list A) (acc : Z) :
  (forall b, 0 <= digit b < 256) -> 0 <= acc ->
  0 <= List.fold_left (fun acc b => 256 * acc + digit b) bytes acc <
    (acc + 1) * 256 ^ Z.of_nat (List.length bytes).
Proof.
  intros Hdigit. revert acc.
  induction bytes as [|b bs IH]; intros acc Hacc; simpl.
  - lia.
  - pose proof (Hdigit b) as Hb.
    specialize (IH (256 * acc + digit b) ltac:(lia)).
    rewrite Nat2Z.inj_succ, Z.pow_succ_r by lia.
    set (X := 256 ^ Z.of_nat (List.length bs)) in *.
    assert (0 < X) by (apply Z.pow_pos_nonneg; lia).
    assert (0 <= (255 - digit b) * X) by (apply Z.mul_nonneg_nonneg; lia).
    lia.
Qed.

Lemma bigEndianFoldBound (bytes : list byte) (acc : Z) :
  0 <= acc ->
  0 <= List.fold_left (fun acc (b : byte) => 256 * acc + bv_unsigned b) bytes acc <
    (acc + 1) * 256 ^ Z.of_nat (List.length bytes).
Proof.
  apply digitFoldBound. intros b.
  pose proof (bv_unsigned_in_range 8 b) as Hr.
  change (bv_modulus 8) with 256 in Hr. exact Hr.
Qed.

Lemma bigEndianBound8 (bytes : list byte) :
  (List.length bytes <= 8)%nat -> 0 <= bigEndian bytes < 2 ^ 64.
Proof.
  intros Hlen.
  assert (Hb : 0 <= bigEndian bytes < (0 + 1) * 256 ^ Z.of_nat (List.length bytes))
    by exact (bigEndianFoldBound bytes 0 ltac:(lia)).
  assert (256 ^ Z.of_nat (List.length bytes) <= 2 ^ 64).
  { change (2 ^ 64) with (256 ^ 8). apply Z.pow_le_mono_r; lia. }
  lia.
Qed.

Lemma itemValueBound (r : list byte) (headerLength payloadLength : Z) :
  payloadLength <= 8 ->
  0 <= bigEndian (firstn (Z.to_nat payloadLength)
                    (skipn (Z.to_nat headerLength) r)) < 2 ^ 64.
Proof.
  intros Hp. apply bigEndianBound8. rewrite firstn_length. lia.
Qed.

Lemma bigEndianNonneg (bytes : list byte) : 0 <= bigEndian bytes.
Proof.
  assert (Hb : 0 <= bigEndian bytes < (0 + 1) * 256 ^ Z.of_nat (List.length bytes))
    by exact (bigEndianFoldBound bytes 0 ltac:(lia)).
  lia.
Qed.

Lemma candidateDecodeItemNonneg (r : list byte) isList headerLength payloadLength :
  candidateDecodeItem r = candidateSuccess isList headerLength payloadLength ->
  0 <= headerLength /\ 0 <= payloadLength.
Proof.
  destruct r as [|b rest]; [discriminate|].
  unfold candidateDecodeItem, checkedPayload. cbv beta iota zeta.
  repeat match goal with
         | |- context [if ?c then _ else _] => destruct c eqn:?
         end;
    intros E; inversion E; subst;
    change (MachineWord.Z_idx 8) with 8%N in *;
    rewrite ?Z.leb_le, ?Z.leb_gt, ?Z.eqb_eq, ?Z.eqb_neq in *;
    split; first [lia | apply bigEndianNonneg].
Qed.

Lemma noWrapDecode (r : list byte) isList headerLength payloadLength :
  candidateDecodeItem r = candidateSuccess isList headerLength payloadLength ->
  candidateWrapb r = false ->
  Z.of_nat (List.length r) < 2 ^ 31 ->
  sailDecodeItem r = candidateSuccess isList headerLength payloadLength /\
  (headerLength + payloadLength) mod word64Modulus = headerLength + payloadLength.
Proof.
  intros Hdec Hwrap Hlen.
  pose proof (candidateDecodeItemNonneg r isList headerLength payloadLength Hdec) as [Hh Hp].
  unfold candidateWrapb in Hwrap. rewrite Hdec in Hwrap.
  apply Z.ltb_ge in Hwrap.
  unfold sailDecodeItem. rewrite Hdec.
  split.
  - destruct (Z.leb_spec (headerLength + payloadLength) (Z.of_nat (List.length r)));
      [reflexivity|lia].
  - unfold word64Modulus. apply Z.mod_small. lia.
Qed.

Lemma nthErrorPast (values : list Z) (n : nat) :
  (List.length values <= n)%nat -> nth_error values n = None.
Proof. apply nth_error_None. Qed.

Lemma nthErrorSnoc (values : list Z) (value : Z) :
  nth_error (values ++ [value]) (List.length values) = Some value.
Proof.
  rewrite nth_error_app2 by lia. rewrite Nat.sub_diag. reflexivity.
Qed.

Lemma nthErrorSnocPast (values : list Z) (value : Z) (n : nat) :
  (List.length values < n)%nat -> nth_error (values ++ [value]) n = None.
Proof.
  intros H. apply nth_error_None. rewrite app_length. simpl. lia.
Qed.

Lemma canonicalNotList r isList h p :
  sailShortUintCanonical r isList h p = true -> isList = false.
Proof.
  unfold sailShortUintCanonical. destruct isList; [discriminate|reflexivity].
Qed.

(* The success branch of a step: reduce both steps to their item tests. *)
Ltac zesu_m2_step_open Hdec Hwrap Hlen :=
  let Hsail := fresh "Hsail" in let Hmod := fresh "Hmod" in
  destruct (noWrapDecode _ _ _ _ Hdec Hwrap Hlen) as [Hsail Hmod];
  cbv beta iota zeta; rewrite Hsail; cbv beta iota zeta; rewrite Hmod.

(* Fields Sail only decodes as items. *)
Lemma skipFieldStep (index : nat) (kind : ParentHeaderFieldKind) :
  parentHeaderFieldIsInteger kind = false ->
  intFieldsBefore (S index) = intFieldsBefore index ->
  (forall r isList h p acc, sailFieldStep index r isList h p acc = Some acc) ->
  FieldStepAgrees index kind.
Proof.
  intros Hkind Hint Hskip r values acc Hne Hlen [Hacc [Hcount Hbound]] Hdiv.
  unfold candidateFieldStep, sailStep. rewrite Hkind.
  destruct (candidateDecodeItem r) as [|isList h p] eqn:Hdec.
  - unfold sailDecodeItem. rewrite Hdec. reflexivity.
  - unfold fieldDivergentb in Hdiv. apply orb_false_iff in Hdiv as [Hwrap _].
    zesu_m2_step_open Hdec Hwrap Hlen.
    rewrite Hskip. cbv beta iota zeta.
    eexists. split; [reflexivity|].
    repeat split; [exact Hacc| rewrite Hint; exact Hcount| exact Hbound].
Qed.

(* Fields 9 to 11: the binary folds an integer, Sail only decodes the item. *)
Lemma undecodedFieldStep (index : nat) (kind : ParentHeaderFieldKind) :
  parentHeaderFieldIsInteger kind = true ->
  (9 <= index <= 11)%nat ->
  intFieldsBefore (S index) = S (intFieldsBefore index) ->
  (intFieldsBefore index < 3)%nat ->
  FieldStepAgrees index kind.
Proof.
  intros Hkind Hrange Hint Hsmall r values acc Hne Hlen [Hacc [Hcount Hbound]] Hdiv.
  unfold candidateFieldStep, sailStep. rewrite Hkind.
  destruct (candidateDecodeItem r) as [|isList h p] eqn:Hdec.
  - unfold sailDecodeItem. rewrite Hdec. reflexivity.
  - unfold fieldDivergentb in Hdiv. apply orb_false_iff in Hdiv as [Hwrap Hdiv].
    rewrite Hdec in Hdiv. cbv beta iota zeta in Hdiv.
    assert (Hz : (index =? 0)%nat || (index =? 3)%nat = false)
      by (apply orb_false_iff; split; apply Nat.eqb_neq; lia).
    assert (Hr : (9 <=? index)%nat && (index <=? 11)%nat = true)
      by (apply andb_true_iff; split; apply Nat.leb_le; lia).
    assert (H15 : (index =? 15)%nat = false) by (apply Nat.eqb_neq; lia).
    assert (H17 : (index =? 17)%nat = false) by (apply Nat.eqb_neq; lia).
    assert (H18 : (index =? 18)%nat = false) by (apply Nat.eqb_neq; lia).
    rewrite Hz, Hr in Hdiv. cbv beta iota in Hdiv.
    zesu_m2_step_open Hdec Hwrap Hlen.
    rewrite Hdiv. cbv beta iota zeta.
    unfold sailFieldStep. rewrite Hz, H15, H17, H18. cbv beta iota zeta.
    apply orb_false_iff in Hdiv as [_ Hp]. apply Z.ltb_ge in Hp.
    eexists. split; [reflexivity|].
    split; [|split].
    + rewrite Hacc. unfold projectValues.
      rewrite !nthErrorSnocPast, !nthErrorPast by lia. reflexivity.
    + rewrite app_length, Hcount, Hint. simpl. lia.
    + apply Forall_app. split; [exact Hbound|].
      constructor; [apply itemValueBound; lia|constructor].
Qed.

(* Fields 0 and 3: rlp_decode_word (a string of at most 32 bytes). *)
Lemma wordFieldStep (index : nat) (kind : ParentHeaderFieldKind) :
  parentHeaderFieldIsInteger kind = false ->
  (index = 0 \/ index = 3)%nat ->
  intFieldsBefore (S index) = intFieldsBefore index ->
  FieldStepAgrees index kind.
Proof.
  intros Hkind Hidx Hint r values acc Hne Hlen [Hacc [Hcount Hbound]] Hdiv.
  unfold candidateFieldStep, sailStep. rewrite Hkind.
  destruct (candidateDecodeItem r) as [|isList h p] eqn:Hdec.
  - unfold sailDecodeItem. rewrite Hdec. reflexivity.
  - unfold fieldDivergentb in Hdiv. apply orb_false_iff in Hdiv as [Hwrap Hdiv].
    rewrite Hdec in Hdiv. cbv beta iota zeta in Hdiv.
    assert (Hz : (index =? 0)%nat || (index =? 3)%nat = true)
      by (destruct Hidx; subst; reflexivity).
    rewrite Hz in Hdiv. cbv beta iota in Hdiv.
    zesu_m2_step_open Hdec Hwrap Hlen.
    unfold sailFieldStep. rewrite Hz. cbv beta iota zeta. rewrite Hdiv.
    eexists. split; [reflexivity|].
    repeat split; [exact Hacc| rewrite Hint; exact Hcount| exact Hbound].
Qed.

(* Fields 15, 17 and 18: rlp_decode_u256 and rlp_decode_uint64 with the
   blob range checks. *)
Lemma integerFieldStep (index : nat) (kind : ParentHeaderFieldKind) (limit : Z)
    (check : Z -> bool) (update : Z -> SailParentValues -> SailParentValues)
    (slot : nat) :
  parentHeaderFieldIsInteger kind = true ->
  intFieldsBefore index = slot ->
  intFieldsBefore (S index) = S slot ->
  8 <= limit ->
  (forall r isList h p acc,
     sailFieldStep index r isList h p acc =
       if sailShortUintCanonical r isList h p && (p <=? limit) &&
          check (bigEndian (itemPayload r h p))
       then Some (update (bigEndian (itemPayload r h p)) acc) else None) ->
  (forall r h p,
     fieldDivergentb index r = false ->
     candidateDecodeItem r = candidateSuccess false h p -> p <= 8 ->
     sailShortUintCanonical r false h p && check (bigEndian (itemPayload r h p)) = true) ->
  (forall r h p,
     fieldDivergentb index r = false ->
     candidateDecodeItem r = candidateSuccess false h p -> 8 < p ->
     sailShortUintCanonical r false h p && (p <=? limit) &&
       check (bigEndian (itemPayload r h p)) = false) ->
  (forall values value, List.length values = slot ->
     update value (projectValues values) = projectValues (values ++ [value])) ->
  FieldStepAgrees index kind.
Proof.
  intros Hkind Hslot Hnext Hlimit Hstep Hok Hover Hupdate
    r values acc Hne Hlen [Hacc [Hcount Hbound]] Hdiv.
  unfold candidateFieldStep, sailStep. rewrite Hkind.
  destruct (candidateDecodeItem r) as [|isList h p] eqn:Hdec.
  - unfold sailDecodeItem. rewrite Hdec. reflexivity.
  - pose proof Hdiv as Hdiv'.
    unfold fieldDivergentb in Hdiv'. apply orb_false_iff in Hdiv' as [Hwrap _].
    zesu_m2_step_open Hdec Hwrap Hlen.
    rewrite Hstep.
    destruct isList.
    + cbn [orb]. cbv beta iota zeta.
      destruct (sailShortUintCanonical r true h p) eqn:Hc; [|reflexivity].
      apply canonicalNotList in Hc. discriminate.
    + cbn [orb]. destruct (Z.ltb_spec 8 p) as [Hp|Hp]; cbv beta iota zeta.
      * rewrite (Hover r h p Hdiv Hdec Hp). reflexivity.
      * specialize (Hok r h p Hdiv Hdec Hp).
        apply andb_true_iff in Hok as [Hc Hchk]. rewrite Hc, Hchk.
        assert (Hle : (p <=? limit) = true) by (apply Z.leb_le; lia).
        rewrite Hle. cbn [andb]. cbv beta iota zeta.
        eexists. split; [reflexivity|].
        split; [|split].
        -- rewrite Hacc. unfold itemPayload. apply Hupdate. lia.
        -- rewrite app_length, Hcount, Hslot, Hnext. simpl. lia.
        -- apply Forall_app. split; [exact Hbound|].
           constructor; [apply itemValueBound; lia|constructor].
Qed.

Lemma projectSnoc3 (values : list Z) (value : Z) :
  List.length values = 3%nat ->
  projectValues (values ++ [value]) =
    {| sailBaseFee := Some value;
       sailBlobGasUsed := sailBlobGasUsed (projectValues values);
       sailExcessBlobGas := sailExcessBlobGas (projectValues values) |}.
Proof.
  intros H. unfold projectValues.
  cbn [sailBaseFee sailBlobGasUsed sailExcessBlobGas].
  assert (E : nth_error (values ++ [value]) 3 = Some value)
    by (rewrite <- H; apply nthErrorSnoc).
  rewrite E, (nthErrorSnocPast values value 4), (nthErrorSnocPast values value 5),
    (nthErrorPast values 4), (nthErrorPast values 5) by lia.
  reflexivity.
Qed.

Lemma projectSnoc4 (values : list Z) (value : Z) :
  List.length values = 4%nat ->
  projectValues (values ++ [value]) =
    {| sailBaseFee := sailBaseFee (projectValues values);
       sailBlobGasUsed := Some value;
       sailExcessBlobGas := sailExcessBlobGas (projectValues values) |}.
Proof.
  intros H. unfold projectValues.
  cbn [sailBaseFee sailBlobGasUsed sailExcessBlobGas].
  assert (E : nth_error (values ++ [value]) 4 = Some value)
    by (rewrite <- H; apply nthErrorSnoc).
  rewrite E, (nthErrorSnocPast values value 5), (nthErrorPast values 5) by lia.
  rewrite (nth_error_app1 values [value] (n := 3%nat)) by lia. reflexivity.
Qed.

Lemma projectSnoc5 (values : list Z) (value : Z) :
  List.length values = 5%nat ->
  projectValues (values ++ [value]) =
    {| sailBaseFee := sailBaseFee (projectValues values);
       sailBlobGasUsed := sailBlobGasUsed (projectValues values);
       sailExcessBlobGas := Some value |}.
Proof.
  intros H. unfold projectValues.
  cbn [sailBaseFee sailBlobGasUsed sailExcessBlobGas].
  assert (E : nth_error (values ++ [value]) 5 = Some value)
    by (rewrite <- H; apply nthErrorSnoc).
  rewrite E, (nth_error_app1 values [value] (n := 3%nat)),
    (nth_error_app1 values [value] (n := 4%nat)) by lia.
  reflexivity.
Qed.

(* fieldDivergentb at an integer field Sail decodes, opened. *)
Ltac zesu_m2_open_divergence Hdiv Hdec :=
  unfold fieldDivergentb in Hdiv; apply orb_false_iff in Hdiv as [_ Hdiv];
  rewrite Hdec in Hdiv; cbv beta iota zeta in Hdiv;
  cbn [Nat.eqb Nat.leb orb andb negb] in Hdiv.

Lemma baseFeeFieldStep : FieldStepAgrees 15 OptionalUint64.
Proof.
  apply (integerFieldStep 15 OptionalUint64 32 (fun _ => true)
    (fun value acc => {| sailBaseFee := Some value;
                         sailBlobGasUsed := sailBlobGasUsed acc;
                         sailExcessBlobGas := sailExcessBlobGas acc |}) 3);
    [reflexivity|reflexivity|reflexivity|lia| | | | ].
  - intros r isList h p acc. unfold sailFieldStep. cbv beta iota zeta.
    cbn [Nat.eqb orb]. rewrite andb_true_r. reflexivity.
  - intros r h p Hdiv Hdec Hp. zesu_m2_open_divergence Hdiv Hdec.
    assert (E1 : (8 <? p) = false) by (apply Z.ltb_ge; lia).
    assert (E2 : (p <=? 8) = true) by (apply Z.leb_le; lia).
    rewrite E1, E2 in Hdiv. cbn [andb orb negb] in Hdiv.
    apply negb_false_iff in Hdiv. rewrite Hdiv. reflexivity.
  - intros r h p Hdiv Hdec Hp. zesu_m2_open_divergence Hdiv Hdec.
    assert (E1 : (8 <? p) = true) by (apply Z.ltb_lt; lia).
    assert (E2 : (p <=? 8) = false) by (apply Z.leb_gt; lia).
    rewrite E1, E2 in Hdiv. cbn [andb orb negb] in Hdiv.
    rewrite orb_false_r in Hdiv. cbv beta. rewrite andb_true_r, andb_comm.
    exact Hdiv.
  - intros values value H. rewrite (projectSnoc3 values value H). reflexivity.
Qed.

Lemma blobGasFieldStep : FieldStepAgrees 17 OptionalUint64.
Proof.
  apply (integerFieldStep 17 OptionalUint64 8
    (fun value => (value / 2 ^ 17 <=? sailBlobMax) && (value =? 2 ^ 17 * (value / 2 ^ 17)))
    (fun value acc => {| sailBaseFee := sailBaseFee acc;
                         sailBlobGasUsed := Some value;
                         sailExcessBlobGas := sailExcessBlobGas acc |}) 4);
    [reflexivity|reflexivity|reflexivity|lia| | | | ].
  - intros r isList h p acc. unfold sailFieldStep. cbv beta iota zeta.
    cbn [Nat.eqb orb]. rewrite !andb_assoc. reflexivity.
  - intros r h p Hdiv Hdec Hp. zesu_m2_open_divergence Hdiv Hdec.
    assert (E2 : (p <=? 8) = true) by (apply Z.leb_le; lia).
    rewrite E2 in Hdiv. cbn [andb] in Hdiv.
    apply negb_false_iff in Hdiv. rewrite <- andb_assoc in Hdiv. exact Hdiv.
  - intros r h p Hdiv Hdec Hp.
    assert (E2 : (p <=? 8) = false) by (apply Z.leb_gt; lia).
    rewrite E2, andb_false_r. reflexivity.
  - intros values value H. rewrite (projectSnoc4 values value H). reflexivity.
Qed.

Lemma excessBlobGasFieldStep : FieldStepAgrees 18 OptionalUint64.
Proof.
  apply (integerFieldStep 18 OptionalUint64 8
    (fun value => value <=? sailExcessBlobGasLimit)
    (fun value acc => {| sailBaseFee := sailBaseFee acc;
                         sailBlobGasUsed := sailBlobGasUsed acc;
                         sailExcessBlobGas := Some value |}) 5);
    [reflexivity|reflexivity|reflexivity|lia| | | | ].
  - intros r isList h p acc. reflexivity.
  - intros r h p Hdiv Hdec Hp. zesu_m2_open_divergence Hdiv Hdec.
    assert (E2 : (p <=? 8) = true) by (apply Z.leb_le; lia).
    rewrite E2 in Hdiv. cbn [andb] in Hdiv.
    apply negb_false_iff in Hdiv. exact Hdiv.
  - intros r h p Hdiv Hdec Hp.
    assert (E2 : (p <=? 8) = false) by (apply Z.leb_gt; lia).
    rewrite E2, andb_false_r. reflexivity.
  - intros values value H. rewrite (projectSnoc5 values value H). reflexivity.
Qed.

Ltac zesu_m2_field :=
  first
    [ apply baseFeeFieldStep
    | apply blobGasFieldStep
    | apply excessBlobGasFieldStep
    | apply wordFieldStep; [reflexivity|lia|reflexivity]
    | apply undecodedFieldStep; [reflexivity|lia|reflexivity|cbv; lia]
    | apply skipFieldStep; [reflexivity|reflexivity|];
      intros; unfold sailFieldStep; reflexivity ].

(* All nineteen fields of parentHeaderFieldSchedule. *)
Lemma scheduleFieldSteps (k : nat) (pc : Z) (kind : ParentHeaderFieldKind) :
  nth_error parentHeaderFieldSchedule k = Some (pc, kind) ->
  FieldStepAgrees k kind.
Proof.
  intros Hk.
  do 19 (destruct k as [|k];
    [cbn in Hk; injection Hk as <- <-; zesu_m2_field|]).
  destruct k; cbn in Hk; discriminate Hk.
Qed.

(* Step 4: composition. *)
Lemma parentHeaderFieldWalkCons (index : nat) (pc : Z)
    (kind : ParentHeaderFieldKind) later (b : byte) (bs : list byte) values :
  snd (parentHeaderFieldWalk index ((pc, kind) :: later) (b :: bs) values) =
  match candidateFieldStep kind (b :: bs) values with
  | candidateStepReject => walkRejectField index
  | candidateStepContinue rest values' =>
      snd (parentHeaderFieldWalk (S index) later rest values')
  end.
Proof.
  cbn [parentHeaderFieldWalk]. unfold candidateFieldStep.
  destruct (candidateDecodeItem (b :: bs)) as [|isList h p]; [reflexivity|].
  cbv beta iota zeta.
  destruct (parentHeaderFieldIsInteger kind); [destruct (isList || (8 <? p))|];
    try reflexivity;
    match goal with
    | |- context [parentHeaderFieldWalk ?i ?l ?r ?v] =>
        destruct (parentHeaderFieldWalk i l r v); reflexivity
    end.
Qed.

Lemma walkAgrees (schedule : list (Z * ParentHeaderFieldKind)) :
  forall index r values acc,
    (forall k pc kind, nth_error schedule k = Some (pc, kind) ->
       FieldStepAgrees (index + k) kind) ->
    Z.of_nat (List.length r) < 2 ^ 31 ->
    sailValuesMatch index values acc ->
    walkNoDivergence index schedule r values = true ->
    match snd (parentHeaderFieldWalk index schedule r values) with
    | walkAccept final =>
        sailFieldWalk index (List.length schedule) r acc = Some (projectValues final) /\
        Forall (fun value => 0 <= value < 2 ^ 64) final
    | walkRejectOuter => False
    | walkMissingField _ | walkRejectField _ =>
        sailFieldWalk index (List.length schedule) r acc = None
    end.
Proof.
  induction schedule as [|[pc kind] later IH];
    intros index r values acc Hsteps Hlen Hmatch Hnd.
  - cbn [walkNoDivergence] in Hnd.
    cbn [parentHeaderFieldWalk snd List.length sailFieldWalk]. rewrite Hnd.
    destruct Hmatch as [Hacc [_ Hbound]]. rewrite Hacc.
    split; [reflexivity|exact Hbound].
  - destruct r as [|b bs].
    + cbn [walkNoDivergence] in Hnd.
      cbn [parentHeaderFieldWalk snd List.length sailFieldWalk].
      revert Hnd. destruct (parentHeaderFieldIsRequired kind);
        cbn [negb]; intros Hnd; [discriminate Hnd|].
      destruct Hmatch as [Hacc [_ Hbound]]. rewrite Hacc.
      split; [reflexivity|exact Hbound].
    + rewrite parentHeaderFieldWalkCons.
      cbn [walkNoDivergence] in Hnd.
      apply andb_true_iff in Hnd as [Hdiv Hnd]. apply negb_true_iff in Hdiv.
      pose proof (Hsteps 0%nat pc kind eq_refl) as Hstep.
      rewrite Nat.add_0_r in Hstep.
      specialize (Hstep (b :: bs) values acc ltac:(discriminate) Hlen Hmatch Hdiv).
      cbn [List.length sailFieldWalk].
      destruct (candidateFieldStep kind (b :: bs) values) as [|rest values'] eqn:Hc;
        try rewrite Hc in Hstep; try rewrite Hc in Hnd.
      * rewrite Hstep. reflexivity.
      * destruct Hstep as [acc' [Hsail Hmatch']]. rewrite Hsail.
        cbv beta iota zeta.
        assert (Hrest : (List.length rest <= List.length (b :: bs))%nat).
        { revert Hc. unfold candidateFieldStep.
          destruct (candidateDecodeItem (b :: bs)) as [|l h p];
            cbv beta iota zeta; [intros Hc; discriminate Hc|].
          destruct (parentHeaderFieldIsInteger kind); [destruct (l || (8 <? p))|];
            intros Hc; try discriminate Hc;
            injection Hc as Hr _; subst rest; rewrite skipn_length; lia. }
        apply (IH (S index) rest values' acc'); [|lia|exact Hmatch'|exact Hnd].
        intros k pc' kind' Hk.
        replace (S index + k)%nat with (index + S k)%nat by lia.
        exact (Hsteps (S k) pc' kind' Hk).
Qed.

Lemma sailOptionalWordOfValues (present : bool) (value : Z) (final : list Z) (n : nat) :
  Forall (fun value => 0 <= value < 2 ^ 64) final ->
  (if present then Some value else None) = nth_error final n ->
  sailOptionalWord present value (nth_error final n).
Proof.
  intros Hbound Heq. destruct present; simpl; [|symmetry; exact Heq].
  split; [symmetry; exact Heq|].
  rewrite Forall_forall in Hbound. apply Hbound.
  apply nth_error_In with n. symmetry. exact Heq.
Qed.

(* The intermediate theorem: the plan's statement of M2 from the three step
   statements. scheduleFieldSteps proves the third. *)
Theorem candidateParentHeader_sail_from_steps
    (Hmodel : SailParentHeaderModel)
    (Hsteps : forall k pc kind, nth_error parentHeaderFieldSchedule k = Some (pc, kind) ->
       FieldStepAgrees k kind)
    (Hcover : KnownBugTriggersCoverDivergences)
    (bytes : list byte) :
  headerFits bytes -> Z.of_nat (List.length bytes) < 2 ^ 31 ->
  (forall bug, List.In bug knownBugs -> parentHeaderBugTrigger bug bytes = false) ->
  parentHeaderSailAgrees bytes.
Proof.
  intros Hfits Hlen Hbugs.
  pose proof (Hcover bytes Hfits Hlen Hbugs) as Hnd.
  pose proof (Hmodel bytes Hfits Hlen) as Hm.
  assert (Hvalid : validInputSlice bytes 0 (Z.of_nat (List.length bytes)) = true).
  { unfold validInputSlice, stateless_input_region_bound.
    rewrite !andb_true_iff, !Z.leb_le. lia. }
  assert (Hreject : sailParentHeaderRun bytes (parentHeaderSailNode bytes) = Reject RlpDecode ->
            ParentHeaderRejects bytes (parentHeaderSailNode bytes)).
  { intros Hrun. split; [exact Hvalid|exact Hrun]. }
  unfold parentHeaderSailAgrees, candidateParentHeader, parentHeaderWalkEnd,
    parentHeaderWalk.
  unfold parentHeaderNoDivergence in Hnd. unfold sailPureParentHeader in Hm.
  destruct (candidateDecodeItem bytes) as [|isList h p] eqn:Hdec;
    try rewrite Hdec in Hnd; try rewrite Hdec in Hm; cbv beta iota in Hnd, Hm |- *;
    [apply Hreject; exact Hm|].
  destruct isList; cbv beta iota in Hnd, Hm |- *; [|apply Hreject; exact Hm].
  destruct (Z.leb_spec (h + p) (Z.of_nat (List.length bytes))) as [Hin|Hout].
  - assert (Hle : (h + p <=? Z.of_nat (List.length bytes)) = true)
      by (apply Z.leb_le; lia).
    try rewrite Hle in Hnd. cbv beta iota in Hnd.
    apply andb_true_iff in Hnd as [Hnd Hwalk].
    apply andb_true_iff in Hnd as [Heq Hpos].
    rewrite Heq in Hm. try rewrite Hpos; try rewrite Hle. cbn [andb]. cbv beta iota.
    assert (Hplen : Z.of_nat (List.length (itemPayload bytes h p)) < 2 ^ 31).
    { unfold itemPayload. rewrite firstn_length, skipn_length. lia. }
    assert (Hmatch0 : sailValuesMatch 0 [] sailNoValues)
      by (split; [reflexivity|split; [reflexivity|constructor]]).
    pose proof (walkAgrees parentHeaderFieldSchedule 0 (itemPayload bytes h p) []
      sailNoValues Hsteps Hplen Hmatch0 Hwalk) as Hw.
    unfold itemPayload in Hw, Hm.
    destruct (snd (parentHeaderFieldWalk 0 parentHeaderFieldSchedule
      (firstn (Z.to_nat p) (skipn (Z.to_nat h) bytes)) [])) as [|i|i|final] eqn:Hend;
      cbv beta iota.
    + destruct Hw.
    + apply Hreject. rewrite Hw in Hm. exact Hm.
    + apply Hreject. rewrite Hw in Hm. exact Hm.
    + destruct Hw as [Hw Hbound]. rewrite Hw in Hm. cbv beta iota in Hm.
      destruct Hm as [fields [Hrun Hvalues]].
      exists fields. split; [split; [exact Hvalid|exact Hrun]|].
      unfold sailValuesOfFields, projectValues in Hvalues.
      injection Hvalues as Hbase Hblob Hexcess.
      unfold ParentHeaderSharedFields, candidateHeaderOfValues.
      cbn [parentBaseFee parentBlobGas parentExcessBlobGas].
      split; [|split]; apply sailOptionalWordOfValues; assumption.
  - assert (Hgt : (h + p <=? Z.of_nat (List.length bytes)) = false)
      by (apply Z.leb_gt; lia).
    assert (Hne : (h + p =? Z.of_nat (List.length bytes)) = false)
      by (apply Z.eqb_neq; lia).
    rewrite Hne in Hm. try rewrite Hgt; rewrite andb_false_r. cbv beta iota.
    apply Hreject. exact Hm.
Qed.

(* The plan's statement follows from the two open steps. *)
Theorem candidateParentHeader_sail_from_model_and_cover
    (Hmodel : SailParentHeaderModel)
    (Hcover : KnownBugTriggersCoverDivergences)
    (bytes : list byte) :
  headerFits bytes -> Z.of_nat (List.length bytes) < 2 ^ 31 ->
  (forall bug, List.In bug knownBugs -> parentHeaderBugTrigger bug bytes = false) ->
  parentHeaderSailAgrees bytes.
Proof.
  apply candidateParentHeader_sail_from_steps;
    [exact Hmodel|exact scheduleFieldSteps|exact Hcover].
Qed.
