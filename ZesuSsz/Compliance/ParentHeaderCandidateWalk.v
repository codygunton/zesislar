(* Step 2.4 M1 (machine implies candidate), the reusable core: the walk
   invariant of candidateParentHeader and one lemma per thing the binary
   decides. Owner: compliance proof. Pure lemmas over contract predicates
   only: decodeItem's C1-B result (C1BResult, what decodeItemCallMeaningLink
   yields) and nextUint64's root result (nextUint64RootResult, what
   nextUint64CallResultLink yields). No sealed callee name, no Iris, no
   automation.

   The invariant [candidateWalkState bytes k cursor remaining acc]: before
   field k of parentHeaderFieldSchedule the machine's cursor is [cursor]
   bytes into the input and [remaining] bytes are left; the candidate walk
   from that point, with the integer values [acc] collected so far, ends
   where the walk of the whole input ends. The machine's window
   [take remaining (drop cursor bytes)] is the spelling of a decodeItem or
   nextUint64 call input in the generated histories, with cursor =
   bv_unsigned pointer - bv_unsigned (parentHeaderInputPointer args) and
   remaining = bv_unsigned length.

   Every exit lemma is then: [candidateWalkStart] from the outer call's
   record, one step lemma per field the path passes, and one terminal lemma
   at the exit ([candidateWalkDone], [candidateWalkAbsent],
   [candidateWalkMissing], [candidateWalkFieldError],
   [candidateWalkIntegerReject], [candidateWalkNextUint64Reject], or one of
   the outer rejections), closed by [parentHeaderCandidateResultError] or
   [parentHeaderCandidateResultSuccess]. *)
From Coq Require Import List ZArith Lia.
From stdpp Require Import base list numbers bitvector.definitions.
Require Import EvmSailRlp.evm_rlp_types.
Require Import ZesuSsz.Contracts.RlpDecodeItem.
Require Import ZesuSsz.Contracts.DecodeItemPayloadBounds.
Require Import ZesuSsz.Contracts.DecodeItemCallFacts.
Require Import ZesuSsz.Contracts.ParentHeader.
Require Import ZesuSsz.Contracts.ParentHeaderRootFacts.
Require Import ZesuSsz.Contracts.Candidates.ParentHeaderDomain.
Require Import ZesuSsz.Contracts.Candidates.ParentHeaderCandidate.

Import ListNotations.
Open Scope Z_scope.

Definition candidateWalkState (bytes : list byte) (k : nat)
    (cursor remaining : Z) (acc : list Z) : Prop :=
  0 <= cursor /\ 0 <= remaining /\
  cursor + remaining <= Z.of_nat (length bytes) /\
  parentHeaderWalkEnd bytes =
    snd (parentHeaderFieldWalk k (drop k parentHeaderFieldSchedule)
      (take (Z.to_nat remaining) (drop (Z.to_nat cursor) bytes)) acc).

(* ---- Lists, words and the walk's unfolding ---- *)

Lemma walkWindowLength (bytes : list byte) cursor remaining :
  0 <= cursor -> 0 <= remaining -> cursor + remaining <= Z.of_nat (length bytes) ->
  length (take (Z.to_nat remaining) (drop (Z.to_nat cursor) bytes)) = Z.to_nat remaining.
Proof. intros. rewrite length_take, length_drop. lia. Qed.

Lemma walkWindowSkip (bytes : list byte) cursor remaining w :
  0 <= cursor -> 0 <= w <= remaining ->
  drop (Z.to_nat w) (take (Z.to_nat remaining) (drop (Z.to_nat cursor) bytes)) =
  take (Z.to_nat (remaining - w)) (drop (Z.to_nat (cursor + w)) bytes).
Proof.
  intros. rewrite skipn_firstn_comm, skipn_skipn.
  f_equal; [lia|]. f_equal. lia.
Qed.

Lemma walkDropSchedule {A} (l : list A) k x :
  nth_error l k = Some x -> drop k l = x :: drop (S k) l.
Proof.
  revert l. induction k as [|k IH]; intros [|y l] H; cbn in *; try discriminate.
  - by injection H as ->.
  - exact (IH l H).
Qed.

Lemma walkFieldCons k pc kind later (remaining : list byte) acc :
  remaining <> [] ->
  snd (parentHeaderFieldWalk k ((pc, kind) :: later) remaining acc) =
  match candidateDecodeItem remaining with
  | candidateError => walkRejectField k
  | candidateSuccess isList headerLength payloadLength =>
      if parentHeaderFieldIsInteger kind then
        if isList || (8 <? payloadLength) then walkRejectField k
        else snd (parentHeaderFieldWalk (S k) later
          (skipn (Z.to_nat ((headerLength + payloadLength) mod word64Modulus)) remaining)
          (acc ++ [bigEndian (firstn (Z.to_nat payloadLength)
                     (skipn (Z.to_nat headerLength) remaining))]))
      else snd (parentHeaderFieldWalk (S k) later
        (skipn (Z.to_nat ((headerLength + payloadLength) mod word64Modulus)) remaining) acc)
  end.
Proof.
  destruct remaining as [|b rest]; [congruence|]. intros _.
  cbn [parentHeaderFieldWalk].
  destruct (candidateDecodeItem (b :: rest)) as [|isList h p]; [reflexivity|].
  destruct (parentHeaderFieldIsInteger kind); [destruct (isList || (8 <? p))|];
    try reflexivity;
    match goal with |- snd (let '(_, _) := ?w in _) = _ => destruct w end; reflexivity.
Qed.

Lemma walkStateEnd bytes k pc kind cursor remaining acc :
  nth_error parentHeaderFieldSchedule k = Some (pc, kind) ->
  candidateWalkState bytes k cursor remaining acc ->
  remaining <> 0 ->
  (take (Z.to_nat remaining) (drop (Z.to_nat cursor) bytes)) <> [] /\
  parentHeaderWalkEnd bytes =
    snd (parentHeaderFieldWalk k ((pc, kind) :: drop (S k) parentHeaderFieldSchedule)
      (take (Z.to_nat remaining) (drop (Z.to_nat cursor) bytes)) acc).
Proof.
  intros Hk (Hc & Hr & Hcr & Hwalk) Hr0.
  rewrite (walkDropSchedule _ _ _ Hk) in Hwalk. split; [|exact Hwalk].
  intros Hnil. pose proof (walkWindowLength bytes cursor remaining Hc Hr Hcr) as Hlen.
  rewrite Hnil in Hlen. cbn in Hlen. lia.
Qed.

Lemma decodeItemStatusBytes (b33 b32 : bv 8) :
  bv_unsigned (bv_concat 16 b33 b32) = bv_unsigned b33 * 256 + bv_unsigned b32.
Proof. apply concatByteUnsigned. reflexivity. Qed.

Lemma decodeItemListBit (b : byte) :
  bv_unsigned b <= 1 ->
  bv_unsigned (bv_and (bv_zero_extend 64 b) (BV 64 1)) = bv_unsigned b.
Proof.
  intros Hb. pose proof (bv_unsigned_in_range _ b) as Hr.
  rewrite bv_and_unsigned, bv_zero_extend_unsigned by (vm_compute; discriminate).
  change (bv_unsigned (BV 64 1)) with 1.
  assert (bv_unsigned b = 0 \/ bv_unsigned b = 1) as [-> | ->] by lia; reflexivity.
Qed.

Lemma littleEndianNonneg (l : list byte) : 0 <= littleEndian l.
Proof.
  induction l as [|b l IH]; cbn [littleEndian]; [lia|].
  pose proof (bv_unsigned_in_range _ b). lia.
Qed.

Lemma bigEndianNonneg (l : list byte) : 0 <= bigEndian l.
Proof.
  unfold bigEndian. assert (H : forall a, 0 <= a ->
    0 <= fold_left (fun acc b => 256 * acc + bv_unsigned b) l a).
  { induction l as [|b l IH]; intros a Ha; cbn [fold_left]; [lia|].
    apply IH. pose proof (bv_unsigned_in_range _ b). lia. }
  apply H. lia.
Qed.

Lemma candidatePayloadNonneg input isList headerLength payloadLength :
  candidateDecodeItem input = candidateSuccess isList headerLength payloadLength ->
  0 <= payloadLength.
Proof.
  destruct input as [|prefix rest]; [discriminate|].
  pose proof (bv_unsigned_in_range _ prefix) as Hp. unfold bv_modulus in Hp.
  unfold candidateDecodeItem, checkedPayload. cbn zeta.
  repeat case_match; intros; simplify_eq;
    rewrite ?Z.leb_le, ?Z.leb_gt, ?Z.eqb_eq, ?Z.eqb_neq in *;
    change (MachineWord.MachineWord.Z_idx 8) with 8%N in *;
    first [lia | apply bigEndianNonneg].
Qed.

(* A nextUint64 error result (word 3 at byte 8) has byte 8 = 3. *)
Lemma nextUint64Error16Byte8 (result : list byte) :
  nextUint64Error16 result -> bv_unsigned (List.nth 8 result (BV 8 0)) = 3.
Proof.
  intros (Hlen & _ & Hlen8 & Hw).
  destruct (skipn 8 result) as [|b rest] eqn:Hs; [discriminate|].
  assert (Hn : List.nth 8 result (BV 8 0) = b).
  { do 8 (destruct result as [|? result]; [cbn in Hlen; discriminate|]).
    cbn in Hs |- *. rewrite skipn_O in Hs. rewrite Hs. reflexivity. }
  rewrite Hn. cbn [firstn littleEndian] in Hw.
  pose proof (littleEndianNonneg (firstn 7 rest)).
  pose proof (bv_unsigned_in_range _ b). unfold bv_modulus in *.
  change (2 ^ Z.of_N 8) with 256 in *. lia.
Qed.

(* ---- decodeItem's C1-B result read at the machine's loads ---- *)

Lemma c1bSuccess ip input before after :
  C1BResult ip input before after ->
  bv_unsigned (bv_concat 16 (List.nth 33 after (BV 8 0)) (List.nth 32 after (BV 8 0))) = 0 ->
  exists isList headerLength payloadLength,
    candidateDecodeItem input = candidateSuccess isList headerLength payloadLength /\
    bv_unsigned (listWord64At8 after) = payloadLength /\
    bv_unsigned (listWord64At24 after) = (headerLength + payloadLength) mod word64Modulus /\
    bv_unsigned (List.nth 16 after (BV 8 0)) = (if isList then 1 else 0) /\
    bv_unsigned (listWord64At0 after) =
      match input with
      | prefix :: _ => if bv_unsigned prefix =? 128 then 1 else ip + headerLength
      | [] => ip + headerLength
      end.
Proof.
  unfold C1BResult, candidateResult40. intros (_ & Hres & _) Hok.
  rewrite decodeItemStatusBytes in Hok.
  pose proof (bv_unsigned_in_range _ (List.nth 33 after (BV 8 0))) as Hb33.
  pose proof (bv_unsigned_in_range _ (List.nth 32 after (BV 8 0))) as Hb32.
  destruct (candidateDecodeItem input) as [|isList h p] eqn:Hc.
  - exfalso. pose proof (byteAtNth _ _ _ (proj2 Hres 32%nat ltac:(lia))) as H32.
    cbn in H32. lia.
  - destruct Hres as (_ & _ & Hw0 & H8 & H16 & H24 & _).
    exists isList, h, p. split; [reflexivity|].
    rewrite (listWord64At8Value _ _ H8), (listWord64At24Value _ _ H24),
      (listWord64At0Value _ _ Hw0), (byteAtNth _ _ _ H16).
    repeat split; reflexivity.
Qed.

Lemma c1bError ip input before after :
  C1BResult ip input before after ->
  bv_unsigned (bv_concat 16 (List.nth 33 after (BV 8 0)) (List.nth 32 after (BV 8 0))) <> 0 ->
  candidateDecodeItem input = candidateError.
Proof.
  unfold C1BResult, candidateResult40. intros (_ & Hres & _) Hbad.
  destruct (candidateDecodeItem input) as [|isList h p]; [reflexivity|].
  exfalso. destruct Hres as (_ & _ & _ & _ & _ & _ & H32 & H33 & _).
  apply byteAtNth in H32. apply byteAtNth in H33.
  rewrite decodeItemStatusBytes, H32, H33 in Hbad. lia.
Qed.

(* ---- Terminal lemmas ---- *)

Lemma parentHeaderCandidateResultError bytes result :
  candidateParentHeader bytes = candidateHeaderError ->
  parentHeaderError80 result ->
  parentHeaderCandidateResult bytes result.
Proof. intros Hc Hr. unfold parentHeaderCandidateResult. by rewrite Hc. Qed.

Lemma parentHeaderCandidateResultSuccess bytes result header :
  candidateParentHeader bytes = candidateHeaderSuccess header ->
  parentHeaderResult80 result header ->
  parentHeaderCandidateResult bytes result.
Proof. intros Hc Hr. unfold parentHeaderCandidateResult. by rewrite Hc. Qed.

Lemma candidateRejectField bytes k :
  parentHeaderWalkEnd bytes = walkRejectField k ->
  candidateParentHeader bytes = candidateHeaderError.
Proof. intros H. unfold candidateParentHeader. by rewrite H. Qed.

Lemma candidateWalkDone bytes cursor remaining acc :
  candidateWalkState bytes 19 cursor remaining acc ->
  candidateParentHeader bytes = candidateHeaderSuccess (candidateHeaderOfValues acc).
Proof.
  intros (_ & _ & _ & Hwalk). unfold candidateParentHeader. rewrite Hwalk.
  reflexivity.
Qed.

(* Nothing left before an optional field: the walk accepts. *)
Lemma candidateWalkAbsent bytes k pc kind cursor acc :
  nth_error parentHeaderFieldSchedule k = Some (pc, kind) ->
  parentHeaderFieldIsRequired kind = false ->
  candidateWalkState bytes k cursor 0 acc ->
  candidateParentHeader bytes = candidateHeaderSuccess (candidateHeaderOfValues acc).
Proof.
  intros Hk Hopt (_ & _ & _ & Hwalk). rewrite (walkDropSchedule _ _ _ Hk) in Hwalk.
  unfold candidateParentHeader. rewrite Hwalk. cbn. by rewrite Hopt.
Qed.

(* Nothing left before a required field: the walk rejects. *)
Lemma candidateWalkMissing bytes k pc kind cursor acc :
  nth_error parentHeaderFieldSchedule k = Some (pc, kind) ->
  parentHeaderFieldIsRequired kind = true ->
  candidateWalkState bytes k cursor 0 acc ->
  candidateParentHeader bytes = candidateHeaderError.
Proof.
  intros Hk Hreq (_ & _ & _ & Hwalk). rewrite (walkDropSchedule _ _ _ Hk) in Hwalk.
  unfold candidateParentHeader. rewrite Hwalk. cbn. by rewrite Hreq.
Qed.

(* The field's decodeItem call fails (status half-word not 0). *)
Lemma candidateWalkFieldError bytes k pc kind cursor remaining acc ip before after :
  nth_error parentHeaderFieldSchedule k = Some (pc, kind) ->
  candidateWalkState bytes k cursor remaining acc ->
  remaining <> 0 ->
  C1BResult ip (take (Z.to_nat remaining) (drop (Z.to_nat cursor) bytes)) before after ->
  bv_unsigned (bv_concat 16 (List.nth 33 after (BV 8 0)) (List.nth 32 after (BV 8 0))) <> 0 ->
  candidateParentHeader bytes = candidateHeaderError.
Proof.
  intros Hk Hs Hr0 Hres Hbad.
  destruct (walkStateEnd _ _ _ _ _ _ _ Hk Hs Hr0) as [Hne Hwalk].
  apply (candidateRejectField _ k). rewrite Hwalk, walkFieldCons by exact Hne.
  by rewrite (c1bError _ _ _ _ Hres Hbad).
Qed.

(* A required field whose call the machine makes without checking that
   anything is left (fields 9 to 11): the call fails, either on an empty
   window (the field is missing) or on the item. *)
Lemma candidateWalkRequiredFieldError bytes k pc kind cursor remaining acc ip before after :
  nth_error parentHeaderFieldSchedule k = Some (pc, kind) ->
  parentHeaderFieldIsRequired kind = true ->
  candidateWalkState bytes k cursor remaining acc ->
  C1BResult ip (take (Z.to_nat remaining) (drop (Z.to_nat cursor) bytes)) before after ->
  bv_unsigned (bv_concat 16 (List.nth 33 after (BV 8 0)) (List.nth 32 after (BV 8 0))) <> 0 ->
  candidateParentHeader bytes = candidateHeaderError.
Proof.
  intros Hk Hreq Hs Hres Hbad.
  destruct (Z.eq_dec remaining 0) as [-> | Hr0].
  - exact (candidateWalkMissing _ _ _ _ _ _ Hk Hreq Hs).
  - exact (candidateWalkFieldError _ _ _ _ _ _ _ _ _ _ Hk Hs Hr0 Hres Hbad).
Qed.

(* ---- Step lemmas ---- *)

(* A skipped field (required or optional): decodeItem succeeds, the cursor
   advances by the consumed length (word 24 of the result). *)
Lemma candidateWalkSkip bytes k pc kind cursor remaining acc ip before after :
  nth_error parentHeaderFieldSchedule k = Some (pc, kind) ->
  parentHeaderFieldIsInteger kind = false ->
  candidateWalkState bytes k cursor remaining acc ->
  remaining <> 0 ->
  C1BResult ip (take (Z.to_nat remaining) (drop (Z.to_nat cursor) bytes)) before after ->
  bv_unsigned (bv_concat 16 (List.nth 33 after (BV 8 0)) (List.nth 32 after (BV 8 0))) = 0 ->
  candidateWalkState bytes (S k)
    (cursor + bv_unsigned (listWord64At24 after))
    (remaining - bv_unsigned (listWord64At24 after)) acc.
Proof.
  intros Hk Hint Hs Hr0 Hres Hok.
  pose proof Hs as (Hc & Hr & Hcr & _).
  destruct (walkStateEnd _ _ _ _ _ _ _ Hk Hs Hr0) as [Hne Hwalk].
  pose proof (decodeItemConsumedInInput _ _ _ _ Hres) as Hw.
  rewrite walkWindowLength in Hw by assumption.
  pose proof (bv_unsigned_in_range _ (listWord64At24 after)) as Hw0.
  destruct (c1bSuccess _ _ _ _ Hres Hok) as (isList & h & p & Hcand & _ & Hcons & _ & _).
  split; [lia|]. split; [lia|]. split; [lia|].
  rewrite Hwalk, walkFieldCons by exact Hne. rewrite Hcand, Hint, <- Hcons.
  rewrite walkWindowSkip by lia. reflexivity.
Qed.

(* The skip step in the machine's registers: the cursor register p and the
   length register l of the call (decodeItem's a1 and a2), advanced as the
   code does (p + consumed, l - consumed, 64-bit). *)
Lemma walkCursorAdd (p w : bv 64) :
  bv_unsigned p + bv_unsigned w < 2 ^ 64 ->
  bv_unsigned (bv_add p w) = bv_unsigned p + bv_unsigned w.
Proof.
  intros H. rewrite bv_add_unsigned. unfold bv_wrap, bv_modulus.
  pose proof (bv_unsigned_in_range _ p). pose proof (bv_unsigned_in_range _ w).
  unfold bv_modulus in *. rewrite Z.mod_small; lia.
Qed.

Lemma walkRemainingSub (l w : bv 64) :
  bv_unsigned w <= bv_unsigned l ->
  bv_unsigned (bv_sub l w) = bv_unsigned l - bv_unsigned w.
Proof.
  intros H. rewrite bv_sub_unsigned. unfold bv_wrap, bv_modulus.
  pose proof (bv_unsigned_in_range _ l). pose proof (bv_unsigned_in_range _ w).
  unfold bv_modulus in *. rewrite Z.mod_small; lia.
Qed.

Lemma walkRemainingNonzero (l w : bv 64) :
  bv_unsigned l <> bv_unsigned w -> bv_unsigned (bv_sub l w) <> 0.
Proof.
  intros H. rewrite bv_sub_unsigned. unfold bv_wrap, bv_modulus.
  pose proof (bv_unsigned_in_range _ l). pose proof (bv_unsigned_in_range _ w).
  unfold bv_modulus in *. change (2 ^ Z.of_N 64) with 18446744073709551616 in *.
  intros Hm. apply H. apply Z.mod_divide in Hm; [|lia].
  destruct Hm as [q Hq]. assert (q = 0) by nia. lia.
Qed.

Lemma candidateWalkSkipMachine bytes k pc kind (ip p l : bv 64) acc before after :
  nth_error parentHeaderFieldSchedule k = Some (pc, kind) ->
  parentHeaderFieldIsInteger kind = false ->
  candidateWalkState bytes k (bv_unsigned p - bv_unsigned ip) (bv_unsigned l) acc ->
  bv_unsigned l <> 0 ->
  C1BResult (bv_unsigned p)
    (take (Z.to_nat (bv_unsigned l)) (drop (Z.to_nat (bv_unsigned p - bv_unsigned ip)) bytes))
    before after ->
  bv_unsigned (bv_concat 16 (List.nth 33 after (BV 8 0)) (List.nth 32 after (BV 8 0))) = 0 ->
  candidateWalkState bytes (S k)
    (bv_unsigned (bv_add p (listWord64At24 after)) - bv_unsigned ip)
    (bv_unsigned (bv_sub l (listWord64At24 after))) acc.
Proof.
  intros Hk Hint Hs Hl0 Hres Hok.
  pose proof Hs as (Hc & Hr & Hcr & _).
  pose proof (decodeItemConsumedInInput _ _ _ _ Hres) as Hw.
  rewrite walkWindowLength in Hw by assumption.
  pose proof Hres as ((_ & Hfit) & _).
  rewrite walkWindowLength in Hfit by assumption.
  pose proof (bv_unsigned_in_range _ (listWord64At24 after)) as Hw0.
  rewrite walkCursorAdd, walkRemainingSub by (unfold word64Modulus in *; lia).
  replace (bv_unsigned p + bv_unsigned (listWord64At24 after) - bv_unsigned ip)
    with (bv_unsigned p - bv_unsigned ip + bv_unsigned (listWord64At24 after)) by lia.
  exact (candidateWalkSkip _ _ _ _ _ _ _ _ _ _ Hk Hint Hs Hl0 Hres Hok).
Qed.

(* An integer field decoded inline (fields 9 to 11): decodeItem succeeds
   with a string (list byte 0) whose payload is at most 8 bytes; the value
   is the big-endian fold of the payload the machine reads at the payload
   pointer (word 0) for the payload length (word 8). *)
Lemma candidateWalkIntegerStep bytes k pc kind cursor remaining acc ip before after value :
  nth_error parentHeaderFieldSchedule k = Some (pc, kind) ->
  parentHeaderFieldIsInteger kind = true ->
  candidateWalkState bytes k cursor remaining acc ->
  remaining <> 0 ->
  C1BResult ip (take (Z.to_nat remaining) (drop (Z.to_nat cursor) bytes)) before after ->
  bv_unsigned (bv_concat 16 (List.nth 33 after (BV 8 0)) (List.nth 32 after (BV 8 0))) = 0 ->
  bv_unsigned (bv_and (bv_zero_extend 64 (List.nth 16 after (BV 8 0))) (BV 64 1)) = 0 ->
  bv_unsigned (listWord64At8 after) <= 8 ->
  value = bigEndian (take (Z.to_nat (bv_unsigned (listWord64At8 after)))
    (drop (Z.to_nat (bv_unsigned (listWord64At0 after) - ip))
      (take (Z.to_nat remaining) (drop (Z.to_nat cursor) bytes)))) ->
  candidateWalkState bytes (S k)
    (cursor + bv_unsigned (listWord64At24 after))
    (remaining - bv_unsigned (listWord64At24 after)) (acc ++ [value]).
Proof.
  intros Hk Hint Hs Hr0 Hres Hok Hstr H8 Hvalue.
  pose proof Hs as (Hc & Hr & Hcr & _).
  destruct (walkStateEnd _ _ _ _ _ _ _ Hk Hs Hr0) as [Hne Hwalk].
  pose proof (decodeItemConsumedInInput _ _ _ _ Hres) as Hw.
  rewrite walkWindowLength in Hw by assumption.
  pose proof (bv_unsigned_in_range _ (listWord64At24 after)) as Hw0.
  destruct (c1bSuccess _ _ _ _ Hres Hok) as (isList & h & p & Hcand & Hp & Hcons & Hlist & Hptr).
  assert (Hbit : bv_unsigned (List.nth 16 after (BV 8 0)) <= 1) by (destruct isList; lia).
  rewrite (decodeItemListBit _ Hbit) in Hstr.
  destruct isList; [lia|].
  destruct (candidateDecodeItemSuccessBounds _ _ _ _ Hcand) as (Hh & _ & H128).
  split; [lia|]. split; [lia|]. split; [lia|].
  rewrite Hwalk, walkFieldCons by exact Hne. rewrite Hcand, Hint, <- Hcons.
  replace (false || (8 <? p)) with false by (symmetry; apply Z.ltb_ge; lia).
  rewrite walkWindowSkip by lia. do 3 f_equal.
  rewrite Hvalue, Hp. f_equal.
  destruct (take (Z.to_nat remaining) (drop (Z.to_nat cursor) bytes)) as [|prefix rest] eqn:E;
    [congruence|].
  destruct (Z.eqb_spec (bv_unsigned prefix) 128) as [E128|E128].
  - rewrite (H128 prefix rest eq_refl E128). reflexivity.
  - rewrite Hptr. by replace (ip + h - ip) with h by lia.
Qed.

(* An integer field decoded inline that the machine rejects: a list, or a
   payload longer than 8 bytes. *)
Lemma candidateWalkIntegerReject bytes k pc kind cursor remaining acc ip before after :
  nth_error parentHeaderFieldSchedule k = Some (pc, kind) ->
  parentHeaderFieldIsInteger kind = true ->
  candidateWalkState bytes k cursor remaining acc ->
  remaining <> 0 ->
  C1BResult ip (take (Z.to_nat remaining) (drop (Z.to_nat cursor) bytes)) before after ->
  bv_unsigned (bv_concat 16 (List.nth 33 after (BV 8 0)) (List.nth 32 after (BV 8 0))) = 0 ->
  (bv_unsigned (bv_and (bv_zero_extend 64 (List.nth 16 after (BV 8 0))) (BV 64 1)) <> 0 \/
   8 < bv_unsigned (listWord64At8 after)) ->
  candidateParentHeader bytes = candidateHeaderError.
Proof.
  intros Hk Hint Hs Hr0 Hres Hok Hbad.
  destruct (walkStateEnd _ _ _ _ _ _ _ Hk Hs Hr0) as [Hne Hwalk].
  destruct (c1bSuccess _ _ _ _ Hres Hok) as (isList & h & p & Hcand & Hp & _ & Hlist & _).
  assert (Hbit : bv_unsigned (List.nth 16 after (BV 8 0)) <= 1) by (destruct isList; lia).
  rewrite (decodeItemListBit _ Hbit) in Hbad.
  apply (candidateRejectField _ k). rewrite Hwalk, walkFieldCons by exact Hne.
  rewrite Hcand, Hint.
  replace (isList || (8 <? p)) with true; [reflexivity|].
  destruct isList; [reflexivity|]. symmetry. apply Z.ltb_lt. lia.
Qed.

(* An optional integer field through nextUint64 (fields 15, 17, 18) on the
   window [take remaining (drop cursor bytes)] at address [base + cursor]:
   success (byte 8 of the result is 0) advances the cursor to the rest the
   callee returns and appends the result word. *)
Lemma candidateWalkNextUint64 bytes k pc kind cursor remaining acc base call ret :
  nth_error parentHeaderFieldSchedule k = Some (pc, kind) ->
  parentHeaderFieldIsInteger kind = true ->
  candidateWalkState bytes k cursor remaining acc ->
  remaining <> 0 ->
  nextInputBytes call = take (Z.to_nat remaining) (drop (Z.to_nat cursor) bytes) ->
  nextInputPointer call = base + cursor ->
  nextUint64RootResult call ret ->
  bv_unsigned (List.nth 8 (nextResultBytes ret) (BV 8 0)) = 0 ->
  candidateWalkState bytes (S k) (nextRestPointer ret - base) (nextRestLength ret)
    (acc ++ [littleEndian (firstn 8 (nextResultBytes ret))]).
Proof.
  intros Hk Hint Hs Hr0 Hin Hip Hroot Hok.
  pose proof Hs as (Hc & Hr & Hcr & _).
  destruct (walkStateEnd _ _ _ _ _ _ _ Hk Hs Hr0) as [Hne Hwalk].
  destruct Hroot as [_ Hroot]. rewrite Hin in Hroot.
  destruct (candidateDecodeItem _) as [|isList h p] eqn:Hcand.
  { exfalso. destruct Hroot as [Herr _].
    rewrite (nextUint64Error16Byte8 _ Herr) in Hok. lia. }
  destruct (isList || (8 <? p)) eqn:Hbad.
  { exfalso. destruct Hroot as [Herr _].
    rewrite (nextUint64Error16Byte8 _ Herr) in Hok. lia. }
  destruct Hroot as ((_ & Hfold & _) & Hrp & Hrl).
  pose proof Hbad as Hbad'. apply orb_false_iff in Hbad' as [_ Hp8]. apply Z.ltb_ge in Hp8.
  destruct (candidateDecodeItemSuccessBounds _ _ _ _ Hcand) as (Hh & Hfit & _).
  pose proof (walkWindowLength bytes cursor remaining Hc Hr Hcr) as Hlen.
  rewrite Hlen in Hfit, Hrl. rewrite Z2Nat.id in Hfit, Hrl by lia.
  pose proof (candidatePayloadNonneg _ _ _ _ Hcand) as Hp0.
  rewrite Z.mod_small in Hfit by (unfold word64Modulus; lia).
  split; [lia|]. split; [lia|]. split; [lia|].
  rewrite Hwalk, walkFieldCons by exact Hne. rewrite Hcand, Hint, Hbad.
  rewrite Z.mod_small by (unfold word64Modulus; lia).
  rewrite walkWindowSkip by lia.
  rewrite Hrp, Hip, Hrl.
  replace (base + cursor + (h + p) - base) with (cursor + (h + p)) by lia.
  destruct Hfold as [_ ->]. reflexivity.
Qed.

(* nextUint64 rejects (byte 8 of the result is not 0): its decodeItem call
   failed, or the item is a list or longer than 8 bytes. *)
Lemma candidateWalkNextUint64Reject bytes k pc kind cursor remaining acc call ret :
  nth_error parentHeaderFieldSchedule k = Some (pc, kind) ->
  parentHeaderFieldIsInteger kind = true ->
  candidateWalkState bytes k cursor remaining acc ->
  remaining <> 0 ->
  nextInputBytes call = take (Z.to_nat remaining) (drop (Z.to_nat cursor) bytes) ->
  nextUint64RootResult call ret ->
  bv_unsigned (List.nth 8 (nextResultBytes ret) (BV 8 0)) <> 0 ->
  candidateParentHeader bytes = candidateHeaderError.
Proof.
  intros Hk Hint Hs Hr0 Hin Hroot Hbad.
  destruct (walkStateEnd _ _ _ _ _ _ _ Hk Hs Hr0) as [Hne Hwalk].
  apply (candidateRejectField _ k).
  destruct Hroot as [_ Hroot]. rewrite Hin in Hroot.
  rewrite Hwalk, walkFieldCons by exact Hne. rewrite Hint.
  destruct (candidateDecodeItem _) as [|isList h p]; [reflexivity|].
  destruct (isList || (8 <? p)); [reflexivity|].
  exfalso. destruct Hroot as ((_ & _ & H8 & _) & _).
  apply byteAtNth in H8. lia.
Qed.

(* ---- The outer item (call 0x800d5cf4 on the whole input) ---- *)

Lemma candidateWalkStart bytes ip before after :
  headerFits bytes ->
  C1BResult ip bytes before after ->
  bv_unsigned (bv_concat 16 (List.nth 33 after (BV 8 0)) (List.nth 32 after (BV 8 0))) = 0 ->
  bv_unsigned (bv_and (bv_zero_extend 64 (List.nth 16 after (BV 8 0))) (BV 64 1)) <> 0 ->
  bv_unsigned (listWord64At8 after) <> 0 ->
  candidateWalkState bytes 0 (bv_unsigned (listWord64At0 after) - ip)
    (bv_unsigned (listWord64At8 after)) [].
Proof.
  intros Hfits Hres Hok Hlist Hlen0.
  destruct (c1bSuccess _ _ _ _ Hres Hok) as (isList & h & p & Hcand & Hp & _ & H16 & Hptr).
  assert (Hbit : bv_unsigned (List.nth 16 after (BV 8 0)) <= 1) by (destruct isList; lia).
  rewrite (decodeItemListBit _ Hbit) in Hlist.
  destruct isList; [|exfalso; apply Hlist; rewrite H16; reflexivity].
  destruct (candidateDecodeItemSuccessBounds _ _ _ _ Hcand) as (Hh & Hfit & H128).
  pose proof (candidateDecodeItemFitsNoWrap _ _ _ _ Hfits Hcand) as Hnw.
  pose proof (bv_unsigned_in_range _ (listWord64At8 after)) as Hp0.
  pose proof (candidatePayloadNonneg _ _ _ _ Hcand) as Hpn.
  rewrite Z.mod_small in Hfit; [|split; [lia|exact Hnw]].
  assert (Hc : bv_unsigned (listWord64At0 after) - ip = h).
  { rewrite Hptr. destruct bytes as [|prefix rest]; [discriminate Hcand|].
    destruct (Z.eqb_spec (bv_unsigned prefix) 128) as [E|E].
    - rewrite (H128 prefix rest eq_refl E) in Hp. lia.
    - lia. }
  rewrite Hc, Hp. rewrite Hp in Hlen0, Hp0.
  split; [lia|]. split; [lia|]. split; [lia|].
  unfold parentHeaderWalkEnd, parentHeaderWalk. rewrite Hcand.
  replace ((0 <? p) && (h + p <=? Z.of_nat (length bytes))) with true
    by (symmetry; apply andb_true_intro; split; [apply Z.ltb_lt | apply Z.leb_le]; lia).
  reflexivity.
Qed.

Lemma candidateOuterDecodeError bytes ip before after :
  C1BResult ip bytes before after ->
  bv_unsigned (bv_concat 16 (List.nth 33 after (BV 8 0)) (List.nth 32 after (BV 8 0))) <> 0 ->
  candidateParentHeader bytes = candidateHeaderError.
Proof.
  intros Hres Hbad. unfold candidateParentHeader, parentHeaderWalkEnd, parentHeaderWalk.
  by rewrite (c1bError _ _ _ _ Hres Hbad).
Qed.

Lemma candidateOuterNotList bytes ip before after :
  C1BResult ip bytes before after ->
  bv_unsigned (bv_concat 16 (List.nth 33 after (BV 8 0)) (List.nth 32 after (BV 8 0))) = 0 ->
  bv_unsigned (bv_and (bv_zero_extend 64 (List.nth 16 after (BV 8 0))) (BV 64 1)) = 0 ->
  candidateParentHeader bytes = candidateHeaderError.
Proof.
  intros Hres Hok Hlist.
  destruct (c1bSuccess _ _ _ _ Hres Hok) as (isList & h & p & Hcand & _ & _ & H16 & _).
  assert (Hbit : bv_unsigned (List.nth 16 after (BV 8 0)) <= 1) by (destruct isList; lia).
  rewrite (decodeItemListBit _ Hbit) in Hlist.
  destruct isList; [exfalso; rewrite H16 in Hlist; discriminate Hlist|].
  unfold candidateParentHeader, parentHeaderWalkEnd, parentHeaderWalk. by rewrite Hcand.
Qed.

Lemma candidateOuterEmpty bytes ip before after :
  C1BResult ip bytes before after ->
  bv_unsigned (bv_concat 16 (List.nth 33 after (BV 8 0)) (List.nth 32 after (BV 8 0))) = 0 ->
  bv_unsigned (listWord64At8 after) = 0 ->
  candidateParentHeader bytes = candidateHeaderError.
Proof.
  intros Hres Hok Hlen0.
  destruct (c1bSuccess _ _ _ _ Hres Hok) as (isList & h & p & Hcand & Hp & _ & _ & _).
  unfold candidateParentHeader, parentHeaderWalkEnd, parentHeaderWalk. rewrite Hcand.
  rewrite Hp in Hlen0. subst p. destruct isList; reflexivity.
Qed.
