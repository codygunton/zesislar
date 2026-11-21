(* Step 2.4 M1, the success exits: the walk with its values. Owner: contract
   fact (pure lemmas over contract predicates; no generated name, no Iris,
   no automation).

   [candidateWalkReachValues bytes k cursor remaining acc]: before field k
   the walk stands at this cursor with the values [acc], or the candidate
   already rejects. Unlike [candidateWalkReach] it keeps the values, so a
   chain over the call records and the loop fold facts of a success history
   ends at a reach whose values are the stored words. The error disjunct is
   excluded at the exit by the success guards of the path (status
   half-words, list bits, payload bounds and the "something left" checks of
   every field), or, while the return packages do not carry those guards,
   by the binder-free fact [parentHeaderAcceptsCount] (the walk accepts with
   that many values).

   One lemma per success kind (which optional fields are present) then
   names the header, and [parentHeaderNoOptionRecord] gives the 16-byte
   None record the success return blocks 0x03bc store. *)
From Coq Require Import List ZArith Lia.
From stdpp Require Import base list numbers bitvector.definitions.
Require Import EvmSailRlp.evm_rlp_types.
Require Import ZesuSsz.Automation2.ByteWindowFold.
Require Import ZesuSsz.Contracts.RlpDecodeItem.
Require Import ZesuSsz.Contracts.DecodeItemPayloadBounds.
Require Import ZesuSsz.Contracts.ParentHeader.
Require Import ZesuSsz.Contracts.ParentHeaderRootFacts.
Require Import ZesuSsz.Contracts.Candidates.ParentHeaderDomain.
Require Import ZesuSsz.Contracts.Candidates.ParentHeaderCandidate.
Require Import ZesuSsz.Contracts.ParentHeaderCandidateWalk.
Require Import ZesuSsz.Contracts.ParentHeaderSuccessFacts.

Import ListNotations.
Open Scope Z_scope.

Definition candidateWalkReachValues (bytes : list byte) (k : nat)
    (cursor remaining : Z) (acc : list Z) : Prop :=
  candidateParentHeader bytes = candidateHeaderError \/
  candidateWalkState bytes k cursor remaining acc.

(* The walk accepts with [n] values: no field rejected, no required field
   missing, and exactly [n] integer fields were present. *)
Definition parentHeaderAcceptsCount (bytes : list byte) (n : nat) : Prop :=
  exists values, parentHeaderWalkEnd bytes = walkAccept values /\ length values = n.

Lemma reachValuesStart bytes ip before after :
  headerFits bytes ->
  C1BResult ip bytes before after ->
  candidateWalkReachValues bytes 0 (bv_unsigned (listWord64At0 after) - ip)
    (bv_unsigned (listWord64At8 after)) [].
Proof.
  intros Hfits Hres.
  destruct (Z.eq_dec (bv_unsigned (bv_concat 16 (List.nth 33 after (BV 8 0))
    (List.nth 32 after (BV 8 0)))) 0) as [Hok|Hbad];
    [|left; exact (candidateOuterDecodeError _ _ _ _ Hres Hbad)].
  destruct (Z.eq_dec (bv_unsigned (bv_and (bv_zero_extend 64 (List.nth 16 after (BV 8 0)))
    (BV 64 1))) 0) as [Hstr|Hlist];
    [left; exact (candidateOuterNotList _ _ _ _ Hres Hok Hstr)|].
  destruct (Z.eq_dec (bv_unsigned (listWord64At8 after)) 0) as [H0|H0];
    [left; exact (candidateOuterEmpty _ _ _ _ Hres Hok H0)|].
  right. exact (candidateWalkStart _ _ _ _ Hfits Hres Hok Hlist H0).
Qed.

(* A skipped field through decodeItem, in the machine's registers. *)
Lemma reachValuesSkip bytes k pc kind (ip p l : bv 64) acc before after :
  nth_error parentHeaderFieldSchedule k = Some (pc, kind) ->
  parentHeaderFieldIsInteger kind = false ->
  (parentHeaderFieldIsRequired kind = true \/ bv_unsigned l <> 0) ->
  candidateWalkReachValues bytes k (bv_unsigned p - bv_unsigned ip) (bv_unsigned l) acc ->
  C1BResult (bv_unsigned p)
    (take (Z.to_nat (bv_unsigned l)) (drop (Z.to_nat (bv_unsigned p - bv_unsigned ip)) bytes))
    before after ->
  candidateWalkReachValues bytes (S k)
    (bv_unsigned (bv_add p (listWord64At24 after)) - bv_unsigned ip)
    (bv_unsigned (bv_sub l (listWord64At24 after))) acc.
Proof.
  intros Hk Hint Hreq [Herr|Hs] Hres; [left; exact Herr|].
  destruct (Z.eq_dec (bv_unsigned l) 0) as [Hl0|Hl0].
  { left. destruct Hreq as [Hreq|Hreq]; [|contradiction].
    rewrite Hl0 in Hs. exact (candidateWalkMissing _ _ _ _ _ _ Hk Hreq Hs). }
  destruct (Z.eq_dec (bv_unsigned (bv_concat 16 (List.nth 33 after (BV 8 0))
    (List.nth 32 after (BV 8 0)))) 0) as [Hok|Hbad];
    [|left; exact (candidateWalkFieldError _ _ _ _ _ _ _ _ _ _ Hk Hs Hl0 Hres Hbad)].
  right. eapply walkStateMachine; [exact Hs|exact Hres|].
  exact (candidateWalkSkip _ _ _ _ _ _ _ _ _ _ Hk Hint Hs Hl0 Hres Hok).
Qed.

(* The value an inline integer field appends is the loop's fold of the
   payload (the fact the loop exits 0x02e4 / 0x0348 / 0x03b0 state). *)
Lemma integerValueFold bytes (ip p l : bv 64) before after isList h pl :
  0 <= bv_unsigned p - bv_unsigned ip ->
  C1BResult (bv_unsigned p)
    (take (Z.to_nat (bv_unsigned l)) (drop (Z.to_nat (bv_unsigned p - bv_unsigned ip)) bytes))
    before after ->
  candidateDecodeItem
    (take (Z.to_nat (bv_unsigned l)) (drop (Z.to_nat (bv_unsigned p - bv_unsigned ip)) bytes)) =
    candidateSuccess isList h pl ->
  bv_unsigned (listWord64At8 after) = pl ->
  pl <= 8 ->
  bv_unsigned (listWord64At0 after) =
    match take (Z.to_nat (bv_unsigned l)) (drop (Z.to_nat (bv_unsigned p - bv_unsigned ip)) bytes) with
    | prefix :: _ => if bv_unsigned prefix =? 128 then 1 else bv_unsigned p + h
    | [] => bv_unsigned p + h
    end ->
  zesu_byte_window_fold bytes
    (Z.to_nat (bv_unsigned (listWord64At0 after) - bv_unsigned ip))
    (Z.to_nat (bv_unsigned (listWord64At8 after))) =
  bigEndian (take (Z.to_nat (bv_unsigned (listWord64At8 after)))
    (drop (Z.to_nat (bv_unsigned (listWord64At0 after) - bv_unsigned p))
      (take (Z.to_nat (bv_unsigned l)) (drop (Z.to_nat (bv_unsigned p - bv_unsigned ip)) bytes)))).
Proof.
  intros Hc _ Hcand Hp H8 Hptr.
  destruct (Z.eq_dec pl 0) as [E0|E0].
  { rewrite Hp, E0. reflexivity. }
  destruct (candidateDecodeItemSuccessBounds _ _ _ _ Hcand) as (Hh & Hfit & H128).
  pose proof (candidatePayloadNonneg _ _ _ _ Hcand) as Hp0.
  rewrite Z.mod_small in Hfit by (unfold word64Modulus; lia).
  rewrite length_take, length_drop in Hfit.
  destruct (take (Z.to_nat (bv_unsigned l)) (drop (Z.to_nat (bv_unsigned p - bv_unsigned ip)) bytes))
    as [|prefix rest] eqn:E; [discriminate Hcand|].
  destruct (Z.eqb_spec (bv_unsigned prefix) 128) as [E128|E128].
  { exfalso. exact (E0 (H128 prefix rest eq_refl E128)). }
  rewrite <- E.
  unfold zesu_byte_window_fold, zesu_big_endian8, bigEndian. f_equal.
  rewrite skipn_firstn_comm, skipn_skipn, firstn_firstn.
  rewrite Hptr, Hp.
  replace (Z.to_nat (bv_unsigned p + h - bv_unsigned p) + Z.to_nat (bv_unsigned p - bv_unsigned ip))%nat
    with (Z.to_nat (bv_unsigned p + h - bv_unsigned ip)) by lia.
  f_equal. lia.
Qed.

(* An inline integer field (9 to 11, all required) whose value register [x]
   holds the loop's fold of the payload. *)
Lemma reachValuesInteger bytes k pc kind (ip p l x : bv 64) acc before after :
  nth_error parentHeaderFieldSchedule k = Some (pc, kind) ->
  parentHeaderFieldIsInteger kind = true ->
  parentHeaderFieldIsRequired kind = true ->
  candidateWalkReachValues bytes k (bv_unsigned p - bv_unsigned ip) (bv_unsigned l) acc ->
  C1BResult (bv_unsigned p)
    (take (Z.to_nat (bv_unsigned l)) (drop (Z.to_nat (bv_unsigned p - bv_unsigned ip)) bytes))
    before after ->
  bv_unsigned x = zesu_byte_window_fold bytes
    (Z.to_nat (bv_unsigned (listWord64At0 after) - bv_unsigned ip))
    (Z.to_nat (bv_unsigned (listWord64At8 after))) ->
  candidateWalkReachValues bytes (S k)
    (bv_unsigned (bv_add p (listWord64At24 after)) - bv_unsigned ip)
    (bv_unsigned (bv_sub l (listWord64At24 after))) (acc ++ [bv_unsigned x]).
Proof.
  intros Hk Hint Hreq [Herr|Hs] Hres Hx; [left; exact Herr|].
  pose proof Hs as (Hc & Hr & Hcr & _).
  destruct (Z.eq_dec (bv_unsigned l) 0) as [Hl0|Hl0].
  { left. rewrite Hl0 in Hs. exact (candidateWalkMissing _ _ _ _ _ _ Hk Hreq Hs). }
  destruct (Z.eq_dec (bv_unsigned (bv_concat 16 (List.nth 33 after (BV 8 0))
    (List.nth 32 after (BV 8 0)))) 0) as [Hok|Hbad];
    [|left; exact (candidateWalkFieldError _ _ _ _ _ _ _ _ _ _ Hk Hs Hl0 Hres Hbad)].
  destruct (Z.eq_dec (bv_unsigned (bv_and (bv_zero_extend 64 (List.nth 16 after (BV 8 0)))
    (BV 64 1))) 0) as [Hstr|Hlist];
    [|left; exact (candidateWalkIntegerReject _ _ _ _ _ _ _ _ _ _ Hk Hint Hs Hl0 Hres Hok
        (or_introl Hlist))].
  destruct (Z_le_gt_dec (bv_unsigned (listWord64At8 after)) 8) as [H8|H8];
    [|left; exact (candidateWalkIntegerReject _ _ _ _ _ _ _ _ _ _ Hk Hint Hs Hl0 Hres Hok
        (or_intror (Z.gt_lt _ _ H8)))].
  right. eapply walkStateMachine; [exact Hs|exact Hres|].
  destruct (c1bSuccess _ _ _ _ Hres Hok) as (isList & h & pl & Hcand & Hp & _ & _ & Hptr).
  rewrite Hx, (integerValueFold bytes ip p l before after isList h pl Hc Hres
    Hcand Hp ltac:(lia) Hptr).
  exact (candidateWalkIntegerStep _ _ _ _ _ _ _ _ _ _ _ Hk Hint Hs Hl0 Hres Hok Hstr H8 eq_refl).
Qed.

(* The walk only appends values. *)
Lemma walkAcceptExtends index schedule remaining acc values :
  snd (parentHeaderFieldWalk index schedule remaining acc) = walkAccept values ->
  exists more, values = acc ++ more.
Proof.
  revert index remaining acc. induction schedule as [|[pc kind] later IH];
    intros index remaining acc; cbn [parentHeaderFieldWalk].
  - intros H. injection H as <-. exists []. by rewrite app_nil_r.
  - destruct remaining as [|b rest].
    + cbn. destruct (parentHeaderFieldIsRequired kind); [discriminate|].
      intros H. injection H as <-. exists []. by rewrite app_nil_r.
    + destruct (candidateDecodeItem (b :: rest)) as [|isList h p]; [discriminate|].
      destruct (parentHeaderFieldIsInteger kind); [destruct (isList || (8 <? p))|].
      * discriminate.
      * destruct (parentHeaderFieldWalk _ _ _ _) as [trace final] eqn:E. cbn. intros ->.
        destruct (IH _ _ _ (f_equal snd E)) as [more ->].
        eexists. rewrite <- app_assoc. reflexivity.
      * destruct (parentHeaderFieldWalk _ _ _ _) as [trace final] eqn:E. cbn. intros ->.
        exact (IH _ _ _ (f_equal snd E)).
Qed.

(* A reach with [n] values and a walk that accepts with [n] values: the
   candidate's header is the one of these values. *)
Lemma reachValuesExact bytes k cursor remaining acc :
  candidateWalkReachValues bytes k cursor remaining acc ->
  parentHeaderAcceptsCount bytes (length acc) ->
  candidateParentHeader bytes = candidateHeaderSuccess (candidateHeaderOfValues acc).
Proof.
  intros Hreach (values & Hend & Hlen).
  destruct Hreach as [Herr|(_ & _ & _ & Hwalk)].
  { exfalso. unfold candidateParentHeader in Herr. rewrite Hend in Herr. discriminate. }
  rewrite Hend in Hwalk. symmetry in Hwalk.
  destruct (walkAcceptExtends _ _ _ _ _ Hwalk) as [more Hv].
  assert (more = []) as ->.
  { destruct more; [reflexivity|]. exfalso. subst values.
    rewrite length_app in Hlen. cbn in Hlen. lia. }
  rewrite app_nil_r in Hv. subst values.
  unfold candidateParentHeader. by rewrite Hend.
Qed.

(* ---- Success kinds ---- *)

Definition parentHeaderNoOptionHeader (gasLimit gasUsed timestamp : Z) : ParentHeaderValue := {|
  parentGasLimit := gasLimit; parentGasUsed := gasUsed; parentTimestamp := timestamp;
  parentBaseFee := None; parentBlobGas := None; parentExcessBlobGas := None |}.

(* Kind "no optional field", path of slot 1: nothing left after field 11. *)
Lemma candidateNoOptionAfterTimestamp bytes cursor gl gu ts :
  candidateWalkState bytes 12 cursor 0 [gl; gu; ts] ->
  candidateParentHeader bytes = candidateHeaderSuccess (parentHeaderNoOptionHeader gl gu ts).
Proof. exact (candidateWalkAbsent _ 12 _ _ _ _ eq_refl eq_refl). Qed.

(* Kind "no optional field", path of slot 4: fields 12 to 14 skipped, nothing
   left before field 15. *)
Lemma candidateNoOptionBeforeBaseFee bytes cursor gl gu ts :
  candidateWalkState bytes 15 cursor 0 [gl; gu; ts] ->
  candidateParentHeader bytes = candidateHeaderSuccess (parentHeaderNoOptionHeader gl gu ts).
Proof. exact (candidateWalkAbsent _ 15 _ _ _ _ eq_refl eq_refl). Qed.

(* The same kind from a value reach and the count fact. *)
Lemma candidateNoOptionOfReach bytes k cursor remaining gl gu ts :
  candidateWalkReachValues bytes k cursor remaining [gl; gu; ts] ->
  parentHeaderAcceptsCount bytes 3 ->
  candidateParentHeader bytes = candidateHeaderSuccess (parentHeaderNoOptionHeader gl gu ts).
Proof. intros Hr Hn. exact (reachValuesExact _ _ _ _ _ Hr Hn). Qed.

(* The None record of the return block 0x03bc: sixteen zero bytes. *)
Definition parentHeaderZeroRecord : list byte :=
  [BV 8 0; BV 8 0; BV 8 0; BV 8 0; BV 8 0; BV 8 0; BV 8 0; BV 8 0;
   BV 8 0; BV 8 0; BV 8 0; BV 8 0; BV 8 0; BV 8 0; BV 8 0; BV 8 0].

Lemma parentHeaderNoOptionRecord : parentHeaderOptionRecord parentHeaderZeroRecord None.
Proof. split; [reflexivity|]. split; [reflexivity|exact I]. Qed.

(* Result of the no-option kind: the three stored words and three None
   records. *)
Lemma parentHeaderNoOptionResult bytes (gasLimit gasUsed timestamp : bv 64) tail :
  candidateParentHeader bytes = candidateHeaderSuccess
    (parentHeaderNoOptionHeader (bv_unsigned gasLimit) (bv_unsigned gasUsed) (bv_unsigned timestamp)) ->
  length tail = 6%nat ->
  parentHeaderCandidateResult bytes
    (parentHeaderSuccessBytes gasLimit gasUsed timestamp
      parentHeaderZeroRecord parentHeaderZeroRecord parentHeaderZeroRecord tail).
Proof.
  intros Hc Htail.
  exact (parentHeaderSuccessResult _ _ _ _ _ _ _ _ _ Hc eq_refl eq_refl eq_refl
    parentHeaderNoOptionRecord parentHeaderNoOptionRecord parentHeaderNoOptionRecord Htail).
Qed.
