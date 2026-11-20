(* Plan step 2.4, M2: the trigger-coverage premise
   KnownBugTriggersCoverDivergences of ParentHeaderSailAgreement.v, proved
   for the approved KnownBug triggers (ParentHeaderBugTriggers.v), and the
   plan's M2 theorem candidateParentHeader_sail with no premise.

   Structure:
   1. The four trace triggers (skipped-field shape, non-canonical integer,
      integer over 8 bytes, undecoded-field rejection) are existsb of one
      per-field test over parentHeaderWalkTrace; fieldTriggerb joins them.
   2. fieldDivergenceCases: a reached field whose item diverges
      (fieldDivergentb) without a length wrap and without a trace trigger is
      a value divergence at field 17 (blob count or alignment) or 18 (excess
      blob gas limit) on a canonical string of at most 8 bytes.
   3. noNestedWrapStep: while the candidate walk and the reached-slice walk
      of nestedWrapOccursb (fieldSlices) agree, a wrapped item of the walk is
      a wrapped call of fieldSlices.
   4. walkCover, by induction on the schedule: with no trigger, the walk has
      no divergence (walkNoDivergence), or a value divergence at field 17 or
      18 is followed by a candidate rejection (an acceptance would fire the
      blob gas or excess blob gas trigger), and then both reject. The
      missing-field case uses the required-field scan, the end of the
      schedule the trailing-item trigger.
   5. knownBugTriggersCoverDivergences adds the outer item: trailing bytes,
      an empty payload (missing required field).
   Owner: compliance proof. *)

From Coq Require Import Bool List ZArith Lia.
From stdpp Require Import bitvector.definitions.
Require Import SailStdpp.MachineWord.
Require Import EvmSailRlp.evm_rlp_types.
Require Import ZesuSsz.Compliance.KnownBugs.
Require Import ZesuSsz.Contracts.RlpDecodeItem.
Require Import ZesuSsz.Contracts.ParentHeader.
Require Import ZesuSsz.Contracts.ParentHeaderRootFacts.
Require Import ZesuSsz.Contracts.ParentHeaderRequiredFields.
Require Import ZesuSsz.Contracts.Candidates.ParentHeaderDomain.
Require Import ZesuSsz.Contracts.Candidates.ParentHeaderCandidate.
Require Import ZesuSsz.Contracts.ParentHeaderSailItems.
Require Import ZesuSsz.Contracts.ParentHeaderBugTriggers.
Require Import ZesuSsz.Contracts.ParentHeaderRung2.
Require Import ZesuSsz.Compliance.ParentHeaderSailAgreement.
Require Import ZesuSsz.Compliance.ParentHeaderSailEvaluation.

Import ListNotations.
Open Scope Z_scope.

(* Section 1: the per-field pieces of the trace triggers. *)

Definition skippedShapeFieldb (field : ParentHeaderReachedField) : bool :=
    reachedFieldAt field [parentHashField; stateRootField] &&
    match candidateDecodeItem (reachedFieldBytes field) with
    | candidateSuccess isList _ payloadLength =>
        isList || (sailWordLengthLimit <? payloadLength)
    | candidateError => false
    end.

Definition nonCanonicalFieldb (field : ParentHeaderReachedField) : bool :=
    if reachedFieldAt field [baseFeeField; blobGasField; excessBlobGasField] then
      match candidateDecodeItem (reachedFieldBytes field) with
      | candidateSuccess false headerLength payloadLength =>
          if payloadLength <=? foldedPayloadLimit then
            negb (sailShortUintCanonical (reachedFieldBytes field) false
                    headerLength payloadLength)
          else false
      | candidateSuccess true _ _ | candidateError => false
      end
    else false.

Definition over8Fieldb (field : ParentHeaderReachedField) : bool :=
    if reachedFieldAt field [baseFeeField] then
      match candidateDecodeItem (reachedFieldBytes field) with
      | candidateSuccess false headerLength payloadLength =>
          if (foldedPayloadLimit <? payloadLength) &&
             (payloadLength <=? sailWordLengthLimit) then
            sailShortUintCanonical (reachedFieldBytes field) false
              headerLength payloadLength
          else false
      | candidateSuccess true _ _ | candidateError => false
      end
    else false.

Definition undecodedFieldb (field : ParentHeaderReachedField) : bool :=
    reachedFieldAt field [gasLimitField; gasUsedField; timestampField] &&
    negb (candidateWrapb (reachedFieldBytes field)) &&
    match candidateDecodeItem (reachedFieldBytes field) with
    | candidateSuccess isList _ payloadLength =>
        isList || (foldedPayloadLimit <? payloadLength)
    | candidateError => false
    end.

Definition fieldTriggerb (field : ParentHeaderReachedField) : bool :=
  skippedShapeFieldb field || nonCanonicalFieldb field || over8Fieldb field ||
  undecodedFieldb field.

Lemma existsbFalseIn {A} (P : A -> bool) (l : list A) (x : A) :
  existsb P l = false -> In x l -> P x = false.
Proof.
  intros H Hin. destruct (P x) eqn:E; [|reflexivity].
  rewrite <- H. symmetry. apply existsb_exists. exists x. split; assumption.
Qed.

Lemma traceTriggersOff (bytes : list byte) :
  skippedFieldShapeb bytes = false -> uintNonCanonicalb bytes = false ->
  uintOver8b bytes = false -> undecodedFieldRejectedb bytes = false ->
  Forall (fun field => fieldTriggerb field = false) (parentHeaderWalkTrace bytes).
Proof.
  intros H1 H2 H3 H4. apply Forall_forall. intros field Hin.
  unfold fieldTriggerb.
  rewrite (existsbFalseIn skippedShapeFieldb _ _ H1 Hin),
    (existsbFalseIn nonCanonicalFieldb _ _ H2 Hin),
    (existsbFalseIn over8Fieldb _ _ H3 Hin),
    (existsbFalseIn undecodedFieldb _ _ H4 Hin).
  reflexivity.
Qed.

(* Section 2: a reached field whose item diverges and fires no trace
   trigger is a value divergence at field 17 or 18. *)

Definition endValueOkb (index : nat) (value : Z) : bool :=
  if (index =? 17)%nat then
    (value / 2 ^ 17 <=? sailBlobMax) && (value =? 2 ^ 17 * (value / 2 ^ 17))
  else if (index =? 18)%nat then value <=? sailExcessBlobGasLimit
  else true.

Lemma fieldDivergenceCases (index : nat) (kind : ParentHeaderFieldKind) (r : list byte) :
  candidateWrapb r = false ->
  fieldTriggerb {| reachedFieldIndex := index; reachedFieldKind := kind;
                   reachedFieldBytes := r |} = false ->
  fieldDivergentb index r = true ->
  (index = 17 \/ index = 18)%nat /\
  exists h p, candidateDecodeItem r = candidateSuccess false h p /\ p <= 8 /\
    sailShortUintCanonical r false h p = true /\
    endValueOkb index (bigEndian (itemPayload r h p)) = false.
Proof.
  intros Hwrap Htrig Hdiv.
  unfold fieldDivergentb in Hdiv. rewrite Hwrap in Hdiv. cbn [orb] in Hdiv.
  unfold fieldTriggerb, skippedShapeFieldb, nonCanonicalFieldb, over8Fieldb,
    undecodedFieldb, reachedFieldAt in Htrig.
  cbn [reachedFieldIndex reachedFieldBytes] in Htrig.
  rewrite Hwrap in Htrig.
  destruct (candidateDecodeItem r) as [|l h p] eqn:Hdec; [discriminate Hdiv|].
  destruct (Z.ltb_spec 8 p), (Z.ltb_spec 32 p), (Z.leb_spec p 8),
    (Z.leb_spec p 32); try lia.
  all: destruct l; [|destruct (sailShortUintCanonical r false h p) eqn:Hc];
    cbn [negb andb orb] in Hdiv, Htrig.
  all: destruct index as
    [|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|index]]]]]]]]]]]]]]]]]]];
    cbn in Hdiv, Htrig |- *; try discriminate Hdiv; try discriminate Htrig.
  all: split; [tauto|]; exists h, p; split; [reflexivity|];
    split; [assumption|]; split; [assumption|].
  all: apply negb_true_iff; exact Hdiv.
Qed.

(* Section 3: shape of the candidate field walk. *)

Definition candidateWalkNext (index : nat) (kind : ParentHeaderFieldKind)
    (later : list (Z * ParentHeaderFieldKind)) (r : list byte) (values : list Z)
    : list ParentHeaderReachedField * ParentHeaderWalkEnd :=
  match candidateFieldStep kind r values with
  | candidateStepReject => ([], walkRejectField index)
  | candidateStepContinue rest values' =>
      parentHeaderFieldWalk (S index) later rest values'
  end.

Lemma fieldWalkCons (index : nat) (pc : Z) (kind : ParentHeaderFieldKind)
    later (b : byte) (bs : list byte) (values : list Z) :
  parentHeaderFieldWalk index ((pc, kind) :: later) (b :: bs) values =
  ({| reachedFieldIndex := index; reachedFieldKind := kind;
      reachedFieldBytes := b :: bs |}
     :: fst (candidateWalkNext index kind later (b :: bs) values),
   snd (candidateWalkNext index kind later (b :: bs) values)).
Proof.
  cbn [parentHeaderFieldWalk]. unfold candidateWalkNext, candidateFieldStep.
  destruct (candidateDecodeItem (b :: bs)) as [|l h p]; [reflexivity|].
  cbv beta iota zeta.
  destruct (parentHeaderFieldIsInteger kind); [destruct (l || (8 <? p))|];
    try reflexivity;
    match goal with
    | |- context [parentHeaderFieldWalk ?i ?s ?r ?v] =>
        destruct (parentHeaderFieldWalk i s r v); reflexivity
    end.
Qed.

Lemma walkNotOuter (schedule : list (Z * ParentHeaderFieldKind)) :
  forall index r values,
    snd (parentHeaderFieldWalk index schedule r values) <> walkRejectOuter.
Proof.
  induction schedule as [|[pc kind] later IH]; intros index r values.
  - discriminate.
  - destruct r as [|b bs].
    + cbn. destruct (parentHeaderFieldIsRequired kind); discriminate.
    + rewrite fieldWalkCons. cbn [snd]. unfold candidateWalkNext.
      destruct (candidateFieldStep kind (b :: bs) values); [discriminate|apply IH].
Qed.

Lemma walkAcceptExtends (schedule : list (Z * ParentHeaderFieldKind)) :
  forall index r values final,
    snd (parentHeaderFieldWalk index schedule r values) = walkAccept final ->
    exists suffix, final = values ++ suffix.
Proof.
  induction schedule as [|[pc kind] later IH]; intros index r values final Hend.
  - cbn in Hend. injection Hend as <-. exists []. rewrite app_nil_r. reflexivity.
  - destruct r as [|b bs].
    + cbn in Hend. destruct (parentHeaderFieldIsRequired kind); [discriminate Hend|].
      injection Hend as <-. exists []. rewrite app_nil_r. reflexivity.
    + rewrite fieldWalkCons in Hend. cbn [snd] in Hend. unfold candidateWalkNext in Hend.
      unfold candidateFieldStep in Hend.
      destruct (candidateDecodeItem (b :: bs)) as [|l h p]; [discriminate Hend|].
      cbv beta iota zeta in Hend.
      destruct (parentHeaderFieldIsInteger kind); [destruct (l || (8 <? p))|].
      * discriminate Hend.
      * destruct (IH _ _ _ _ Hend) as [suffix ->].
        eexists. rewrite <- app_assoc. reflexivity.
      * exact (IH _ _ _ _ Hend).
Qed.

Lemma walkOptionalNoMissing (schedule : list (Z * ParentHeaderFieldKind)) :
  forallb (fun entry => negb (parentHeaderFieldIsRequired (snd entry))) schedule = true ->
  forall index r values i,
    snd (parentHeaderFieldWalk index schedule r values) <> walkMissingField i.
Proof.
  induction schedule as [|[pc kind] later IH]; intros Hopt index r values i.
  - discriminate.
  - cbn [forallb snd] in Hopt. apply andb_true_iff in Hopt as [Hk Hopt].
    destruct r as [|b bs].
    + cbn. destruct (parentHeaderFieldIsRequired kind); [discriminate Hk|discriminate].
    + rewrite fieldWalkCons. cbn [snd]. unfold candidateWalkNext.
      destruct (candidateFieldStep kind (b :: bs) values); [discriminate|apply IH, Hopt].
Qed.

Lemma skipnConsNth {A} (n : nat) (l : list A) (x : A) (t : list A) :
  skipn n l = x :: t -> nth_error l n = Some x /\ skipn (S n) l = t.
Proof.
  revert l. induction n as [|n IH]; intros [|y l] H; cbn in *; try discriminate.
  - injection H as -> ->. split; reflexivity.
  - apply IH. exact H.
Qed.

(* Section 4: decodeItem facts and the reached-slice walk of
   nestedWrapOccursb. *)

Lemma decodeFacts (r : list byte) l h p :
  candidateDecodeItem r = candidateSuccess l h p ->
  0 <= h /\ 0 <= p /\ 0 < h + p /\
  (h + p) mod word64Modulus <= Z.of_nat (List.length r).
Proof.
  intros Hdec. pose proof (candidateDecodeItemNonneg r l h p Hdec) as [Hh Hp].
  destruct r as [|b rest]; [discriminate|].
  revert Hdec. unfold candidateDecodeItem, checkedPayload. cbv beta iota zeta.
  cbn [List.length].
  repeat match goal with
         | |- context [if ?c then _ else _] => destruct c eqn:?
         end;
    intros E; inversion E; subst;
    change (MachineWord.Z_idx 8) with 8%N in *;
    rewrite ?Z.leb_le, ?Z.leb_gt, ?Z.eqb_eq, ?Z.eqb_neq in *;
    unfold word64Modulus in *; change (Z.pow_pos 2 64) with (2 ^ 64) in *;
    repeat split; first [assumption | lia | rewrite Z.mod_small; lia].
Qed.

Lemma wrapNeedsCarry (r : list byte) l h p :
  candidateDecodeItem r = candidateSuccess l h p ->
  candidateWrapb r = true -> word64Modulus <= h + p.
Proof.
  intros Hdec Hw. pose proof (decodeFacts r l h p Hdec) as (Hh & Hp & Hpos & Hmod).
  unfold candidateWrapb in Hw. rewrite Hdec in Hw. apply Z.ltb_lt in Hw.
  unfold word64Modulus in *.
  destruct (Z.ltb_spec (h + p) (2 ^ 64)); [|lia].
  rewrite Z.mod_small in Hmod; lia.
Qed.

Definition nestedWrapCallb (call : Z * list byte) : bool :=
  let '(pc, remaining) := call in
  negb (pc =? 0x800d5cf4) &&
  existsb (Z.eqb pc)
    (parentHeaderDecodeItemCallSites ++ parentHeaderNextUint64CallSites) &&
  match candidateDecodeItem remaining with
  | candidateSuccess _ headerLength payloadLength =>
      (0 <=? headerLength) && (0 <=? payloadLength) &&
      (word64Modulus <=? headerLength + payloadLength)
  | candidateError => false
  end.

Lemma nestedWrapOccursbSlices (bytes : list byte) :
  nestedWrapOccursb bytes =
  match fieldSlices bytes with
  | Some slices => existsb nestedWrapCallb slices
  | None => false
  end.
Proof. reflexivity. Qed.

Definition callSitePcb (pc : Z) : bool :=
  negb (pc =? 0x800d5cf4) &&
  existsb (Z.eqb pc)
    (parentHeaderDecodeItemCallSites ++ parentHeaderNextUint64CallSites).

Lemma scheduleCallSites :
  forallb (fun entry => callSitePcb (fst entry)) parentHeaderFieldSchedule = true.
Proof. vm_compute. reflexivity. Qed.

Definition NoNestedWrap (schedule : list (Z * ParentHeaderFieldKind))
    (r : list byte) : Prop :=
  forall slices, reachedFieldSlices schedule r = Some slices ->
    existsb nestedWrapCallb slices = false.

Lemma reachedFieldSlicesHead (pc : Z) (kind : ParentHeaderFieldKind) later
    (b : byte) (bs : list byte) slices :
  reachedFieldSlices ((pc, kind) :: later) (b :: bs) = Some slices ->
  exists tail, slices = (pc, b :: bs) :: tail.
Proof.
  cbn [reachedFieldSlices].
  destruct (candidateDecodeItem (b :: bs)) as [|l h p];
    [intros H; injection H as <-; eexists; reflexivity|].
  destruct (positiveItemWithin (b :: bs) h p);
    [|intros H; injection H as <-; eexists; reflexivity].
  destruct (match kind with
            | RequiredSkip | OptionalSkip => false
            | RequiredUint64 | OptionalUint64 => l || (8 <? p)
            end); [intros H; injection H as <-; eexists; reflexivity|].
  destruct (reachedFieldSlices later _); cbn [option_map]; intros H;
    [injection H as <-; eexists; reflexivity|discriminate H].
Qed.

Lemma reachedFieldSlicesSome (schedule : list (Z * ParentHeaderFieldKind)) :
  forall r, exists slices, reachedFieldSlices schedule r = Some slices.
Proof.
  induction schedule as [|[pc kind] later IH]; intros r.
  - eexists. reflexivity.
  - cbn [reachedFieldSlices].
    destruct r as [|b bs]; [destruct kind; eexists; reflexivity|].
    destruct (candidateDecodeItem (b :: bs)) as [|l h p]; [eexists; reflexivity|].
    destruct (positiveItemWithin (b :: bs) h p); [|eexists; reflexivity].
    destruct (match kind with
              | RequiredSkip | OptionalSkip => false
              | RequiredUint64 | OptionalUint64 => l || (8 <? p)
              end); [eexists; reflexivity|].
    destruct (IH (skipn (Z.to_nat (h + p)) (b :: bs))) as [tail ->].
    eexists. reflexivity.
Qed.

Lemma noNestedWrapStep (pc : Z) (kind : ParentHeaderFieldKind) later
    (b : byte) (bs : list byte) l h p :
  callSitePcb pc = true ->
  NoNestedWrap ((pc, kind) :: later) (b :: bs) ->
  candidateDecodeItem (b :: bs) = candidateSuccess l h p ->
  candidateWrapb (b :: bs) = false /\
  (parentHeaderFieldIsInteger kind && (l || (8 <? p)) = false ->
   NoNestedWrap later (skipn (Z.to_nat (h + p)) (b :: bs))).
Proof.
  intros Hpc Hnw Hdec.
  pose proof (decodeFacts _ l h p Hdec) as (Hh & Hp & Hpos & Hmod).
  destruct (reachedFieldSlicesSome ((pc, kind) :: later) (b :: bs)) as [slices Hs].
  destruct (reachedFieldSlicesHead pc kind later b bs slices Hs) as [tail ->].
  pose proof (Hnw _ Hs) as Hf. cbn [existsb] in Hf.
  apply orb_false_iff in Hf as [Hhead _].
  assert (Hwrap : candidateWrapb (b :: bs) = false).
  { destruct (candidateWrapb (b :: bs)) eqn:Hw; [|reflexivity].
    pose proof (wrapNeedsCarry _ l h p Hdec Hw) as Hc.
    unfold nestedWrapCallb in Hhead. unfold callSitePcb in Hpc.
    rewrite Hpc, Hdec in Hhead. cbn [andb] in Hhead.
    apply Z.leb_le in Hc. apply Z.leb_le in Hh. apply Z.leb_le in Hp.
    rewrite Hh, Hp, Hc in Hhead. discriminate Hhead. }
  split; [exact Hwrap|].
  intros Hint later_slices Hlater.
  assert (Hwithin : positiveItemWithin (b :: bs) h p = true).
  { unfold positiveItemWithin. unfold candidateWrapb in Hwrap. rewrite Hdec in Hwrap.
    apply Z.ltb_ge in Hwrap. apply andb_true_iff.
    split; [apply Z.ltb_lt|apply Z.leb_le]; lia. }
  assert (Hm : match kind with
               | RequiredSkip | OptionalSkip => false
               | RequiredUint64 | OptionalUint64 => l || (8 <? p)
               end = false) by (destruct kind; exact Hint).
  assert (Hall : reachedFieldSlices ((pc, kind) :: later) (b :: bs) =
                 Some ((pc, b :: bs) :: later_slices)).
  { cbn [reachedFieldSlices]. rewrite Hdec, Hwithin, Hm, Hlater. reflexivity. }
  pose proof (Hnw _ Hall) as Hf. cbn [existsb] in Hf.
  apply orb_false_iff in Hf as [_ Hf]. exact Hf.
Qed.

(* Section 5: facts of the concrete schedule. *)

Fixpoint requiredPrefix (schedule : list (Z * ParentHeaderFieldKind)) : list bool :=
  match schedule with
  | [] => []
  | (_, kind) :: later =>
      if parentHeaderFieldIsRequired kind
      then parentHeaderFieldIsInteger kind :: requiredPrefix later else []
  end.

Lemma requiredPrefixSchedule :
  requiredPrefix parentHeaderFieldSchedule = requiredParentFields.
Proof. reflexivity. Qed.

Lemma scheduleFacts (index : nat) (pc : Z) (kind : ParentHeaderFieldKind) :
  nth_error parentHeaderFieldSchedule index = Some (pc, kind) ->
  intFieldsBefore (S index) =
    (intFieldsBefore index + if parentHeaderFieldIsInteger kind then 1 else 0)%nat /\
  (parentHeaderFieldIsRequired kind = false ->
   requiredPrefix (skipn (S index) parentHeaderFieldSchedule) = []) /\
  ((index = 17 \/ index = 18)%nat ->
   kind = OptionalUint64 /\
   forallb (fun entry => negb (parentHeaderFieldIsRequired (snd entry)))
     (skipn (S index) parentHeaderFieldSchedule) = true).
Proof.
  intros Hk.
  destruct index as
    [|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|index]]]]]]]]]]]]]]]]]]];
    cbn in Hk; [..|destruct index; discriminate Hk].
  all: injection Hk as <- <-; split; [reflexivity|];
    split; [intros H; first [discriminate H|reflexivity]|];
    intros [H|H]; first [discriminate H|split; reflexivity].
Qed.

(* Section 6: the walk induction. *)

Definition EndValuesOk (final : list Z) : Prop :=
  forall (index : nat) (value : Z), (index = 17 \/ index = 18)%nat ->
    nth_error final (intFieldsBefore index) = Some value ->
    endValueOkb index value = true.

Lemma walkCover (schedule : list (Z * ParentHeaderFieldKind)) :
  forall index r values,
    skipn index parentHeaderFieldSchedule = schedule ->
    Z.of_nat (List.length r) < 2 ^ 31 ->
    List.length values = intFieldsBefore index ->
    NoNestedWrap schedule r ->
    scanRequiredFields (requiredPrefix schedule) r <> RequiredMissing ->
    Forall (fun field => fieldTriggerb field = false)
      (fst (parentHeaderFieldWalk index schedule r values)) ->
    (forall final, snd (parentHeaderFieldWalk index schedule r values) = walkAccept final ->
       EndValuesOk final) ->
    (forall rest, parentHeaderWalkRest schedule r values = Some rest ->
       sailSkipItems (List.length rest) rest = true) ->
    walkNoDivergence index schedule r values = true \/
    ((exists i, snd (parentHeaderFieldWalk index schedule r values) = walkRejectField i) /\
     forall acc, sailValuesMatch index values acc ->
       sailFieldWalk index (List.length schedule) r acc = None).
Proof.
  induction schedule as [|[pc kind] later IH];
    intros index r values Hsched Hlen Hvlen Hnw Hscan Htrace Hend Hrest.
  - left. cbn [walkNoDivergence]. apply Hrest. reflexivity.
  - destruct (skipnConsNth _ _ _ _ Hsched) as [Hnth Hlater].
    destruct (scheduleFacts index pc kind Hnth) as (Hcount & Hopt & H1718).
    assert (Hpc : callSitePcb pc = true).
    { pose proof scheduleCallSites as Hall. rewrite forallb_forall in Hall.
      exact (Hall (pc, kind) (nth_error_In _ _ Hnth)). }
    destruct r as [|b bs].
    + left. cbn [walkNoDivergence].
      destruct (parentHeaderFieldIsRequired kind) eqn:Hreq; [|reflexivity].
      exfalso. apply Hscan. cbn [requiredPrefix]. rewrite Hreq. reflexivity.
    + rewrite fieldWalkCons in Htrace, Hend |- *. cbn [fst snd] in Htrace, Hend |- *.
      apply Forall_cons_iff in Htrace as [Hhere Htail].
      destruct (candidateDecodeItem (b :: bs)) as [|l h p] eqn:Hdec.
      * left. cbn [walkNoDivergence]. unfold fieldDivergentb, candidateWrapb.
        rewrite Hdec. unfold candidateFieldStep. rewrite Hdec. reflexivity.
      * destruct (noNestedWrapStep pc kind later b bs l h p Hpc Hnw Hdec)
          as [Hwrap Hnwtail].
        destruct (noWrapDecode _ l h p Hdec Hwrap Hlen) as [Hsdec Hmod].
        destruct (fieldDivergentb index (b :: bs)) eqn:Hdiv.
        -- destruct (fieldDivergenceCases index kind (b :: bs) Hwrap Hhere Hdiv)
             as [Hidx (h' & p' & Hdec' & Hp8 & Hcanon & Hbad)].
           rewrite Hdec in Hdec'. injection Hdec' as -> <- <-.
           destruct (H1718 Hidx) as [-> Hoptlater].
           rewrite Hlater in Hoptlater.
           assert (Hstep : candidateFieldStep OptionalUint64 (b :: bs) values =
             candidateStepContinue (skipn (Z.to_nat (h + p)) (b :: bs))
               (values ++ [bigEndian (itemPayload (b :: bs) h p)])).
           { unfold candidateFieldStep. rewrite Hdec, Hmod.
             cbn [parentHeaderFieldIsInteger orb].
             destruct (Z.ltb_spec 8 p); [lia|]. reflexivity. }
           unfold candidateWalkNext in Hend |- *. rewrite Hstep in Hend |- *.
           right. split.
           ++ destruct (snd (parentHeaderFieldWalk (S index) later _ _))
                as [|i|i|final] eqn:Hw.
              ** exfalso. exact (walkNotOuter _ _ _ _ Hw).
              ** exfalso. exact (walkOptionalNoMissing later Hoptlater _ _ _ i Hw).
              ** exists i. reflexivity.
              ** exfalso. destruct (walkAcceptExtends _ _ _ _ _ Hw) as [suffix Hfinal].
                 assert (Hnthv : nth_error final (intFieldsBefore index) =
                                 Some (bigEndian (itemPayload (b :: bs) h p))).
                 { rewrite Hfinal, <- Hvlen, <- app_assoc.
                   rewrite nth_error_app2 by lia. rewrite Nat.sub_diag. reflexivity. }
                 pose proof (Hend final eq_refl index _ Hidx Hnthv) as Hok.
                 rewrite Hok in Hbad. discriminate Hbad.
           ++ intros acc _. cbn [List.length sailFieldWalk].
              unfold sailStep. rewrite Hsdec.
              assert (Hnone : sailFieldStep index (b :: bs) false h p acc = None).
              { unfold endValueOkb in Hbad. unfold sailFieldStep. cbv zeta.
                rewrite Hcanon.
                assert (Hp8b : (p <=? 8) = true) by (apply Z.leb_le; lia).
                rewrite Hp8b.
                destruct Hidx as [-> | ->]; cbn [Nat.eqb orb andb] in Hbad |- *;
                  rewrite Hbad; reflexivity. }
              rewrite Hnone. reflexivity.
        -- destruct (candidateFieldStep kind (b :: bs) values) as [|rest values'] eqn:Hstep.
           ++ left. cbn [walkNoDivergence]. rewrite Hdiv, Hstep. reflexivity.
           ++ assert (Hfacts : rest = skipn (Z.to_nat (h + p)) (b :: bs) /\
                  parentHeaderFieldIsInteger kind && (l || (8 <? p)) = false /\
                  values' = if parentHeaderFieldIsInteger kind
                            then values ++ [bigEndian (itemPayload (b :: bs) h p)]
                            else values).
              { revert Hstep. unfold candidateFieldStep. rewrite Hdec, Hmod.
                destruct (parentHeaderFieldIsInteger kind); [destruct (l || (8 <? p))|];
                  intros Hs; try discriminate Hs; injection Hs as <- <-;
                  repeat split; reflexivity. }
              destruct Hfacts as (-> & Hint & Hvalues).
              assert (Hlen' : Z.of_nat (List.length (skipn (Z.to_nat (h + p)) (b :: bs)))
                              < 2 ^ 31) by (rewrite skipn_length; lia).
              assert (Hvlen' : List.length values' = intFieldsBefore (S index)).
              { rewrite Hcount, Hvalues, <- Hvlen.
                destruct (parentHeaderFieldIsInteger kind);
                  [rewrite app_length; cbn; lia|lia]. }
              assert (Hscan' : scanRequiredFields (requiredPrefix later)
                                 (skipn (Z.to_nat (h + p)) (b :: bs)) <> RequiredMissing).
              { destruct (parentHeaderFieldIsRequired kind) eqn:Hreq.
                - intros Hm. apply Hscan. cbn [requiredPrefix]. rewrite Hreq.
                  cbn [scanRequiredFields]. rewrite Hdec.
                  pose proof (decodeFacts _ l h p Hdec) as (_ & _ & Hpos & _).
                  assert (Hwithin : requiredItemWithin (b :: bs) h p = true).
                  { unfold requiredItemWithin. unfold candidateWrapb in Hwrap.
                    rewrite Hdec in Hwrap. apply Z.ltb_ge in Hwrap.
                    apply andb_true_iff. split; [apply Z.ltb_lt|apply Z.leb_le]; lia. }
                  assert (Hc : negb (parentHeaderFieldIsInteger kind) ||
                               (negb l && (p <=? 8)) = true).
                  { destruct (parentHeaderFieldIsInteger kind), l; cbn in Hint |- *;
                      try reflexivity; try discriminate Hint.
                    apply Z.leb_le. apply Z.ltb_ge in Hint. exact Hint. }
                  rewrite Hwithin, Hc. exact Hm.
                - rewrite <- Hlater, (Hopt eq_refl). discriminate. }
              unfold candidateWalkNext in Htail, Hend |- *. rewrite Hstep in Htail, Hend |- *.
              assert (Hrest' : forall rest',
                parentHeaderWalkRest later (skipn (Z.to_nat (h + p)) (b :: bs)) values' =
                  Some rest' -> sailSkipItems (List.length rest') rest' = true).
              { intros rest' Hr. apply Hrest. cbn [parentHeaderWalkRest].
                rewrite Hstep. exact Hr. }
              destruct (IH (S index) _ values' Hlater Hlen' Hvlen' (Hnwtail Hint) Hscan'
                Htail Hend Hrest') as [Hnd|[Hrej Hsail]].
              ** left. cbn [walkNoDivergence]. rewrite Hdiv, Hstep. exact Hnd.
              ** right. split; [exact Hrej|].
                 intros acc Hmatch.
                 pose proof (scheduleFieldSteps index pc kind Hnth) as Hagree.
                 specialize (Hagree (b :: bs) values acc ltac:(discriminate) Hlen Hmatch Hdiv).
                 rewrite Hstep in Hagree. destruct Hagree as [acc' [Hs Hm']].
                 cbn [List.length sailFieldWalk]. rewrite Hs. exact (Hsail acc' Hm').
Qed.

(* Section 7: the coverage premise. *)

Theorem knownBugTriggersCoverDivergences : KnownBugTriggersCoverDivergences.
Proof.
  intros bytes _ Hlen Hbugs.
  pose proof (Hbugs RlpLongLengthWrap ltac:(cbn; tauto)) as Hnest.
  pose proof (Hbugs ParentHeaderMissingRequiredField ltac:(cbn; tauto)) as Hmiss.
  pose proof (Hbugs ParentHeaderTrailingBytes ltac:(cbn; tauto)) as Htrail.
  pose proof (Hbugs ParentHeaderSkippedFieldShape ltac:(cbn; tauto)) as Hshape.
  pose proof (Hbugs ParentHeaderBlobGasUnaligned ltac:(cbn; tauto)) as Hblob.
  pose proof (Hbugs RlpUintNonCanonical ltac:(cbn; tauto)) as Hcanon.
  pose proof (Hbugs ParentHeaderUintOver8 ltac:(cbn; tauto)) as Hover.
  pose proof (Hbugs ParentHeaderUndecodedFieldRejected ltac:(cbn; tauto)) as Hundec.
  pose proof (Hbugs ParentHeaderExcessBlobGasAboveLimit ltac:(cbn; tauto)) as Hexcess.
  pose proof (Hbugs ParentHeaderTrailingItemMalformed ltac:(cbn; tauto)) as Hitem.
  cbn [parentHeaderBugTrigger] in Hnest, Hmiss, Htrail, Hshape, Hblob, Hcanon, Hover,
    Hundec, Hexcess, Hitem.
  unfold parentHeaderNoDivergence.
  destruct (candidateDecodeItem bytes) as [|l h p] eqn:Hdec; [left; reflexivity|].
  destruct l; [|left; reflexivity].
  destruct (Z.leb_spec (h + p) (Z.of_nat (List.length bytes))) as [Hin|Hout];
    [|left; reflexivity].
  pose proof (decodeFacts _ true h p Hdec) as (Hh & Hp & Hpos & _).
  assert (Heq : h + p = Z.of_nat (List.length bytes)).
  { unfold trailingBytesb in Htrail. rewrite Hdec in Htrail.
    apply Z.ltb_ge in Htrail. lia. }
  assert (Hwithin : requiredItemWithin bytes h p = true).
  { unfold requiredItemWithin. apply andb_true_iff.
    split; [apply Z.ltb_lt|apply Z.leb_le]; lia. }
  assert (Hscan : scanRequiredFields requiredParentFields (itemPayload bytes h p)
                  <> RequiredMissing).
  { unfold missingRequiredFieldb, parentHeaderRequiredScan in Hmiss.
    rewrite Hdec, Hwithin in Hmiss. cbn [andb] in Hmiss. unfold itemPayload.
    intros Hm. rewrite Hm in Hmiss. discriminate Hmiss. }
  assert (Hp0 : 0 < p).
  { destruct (Z.ltb_spec 0 p) as [|Hle]; [assumption|]. exfalso. apply Hscan.
    replace p with 0 by lia. reflexivity. }
  assert (Houter : (0 <? p) && (h + p <=? Z.of_nat (List.length bytes)) = true).
  { apply andb_true_iff. split; [apply Z.ltb_lt|apply Z.leb_le]; lia. }
  assert (Hwalk : parentHeaderWalk bytes =
    parentHeaderFieldWalk 0 parentHeaderFieldSchedule (itemPayload bytes h p) []).
  { unfold parentHeaderWalk. rewrite Hdec, Houter. reflexivity. }
  assert (Hnw : NoNestedWrap parentHeaderFieldSchedule (itemPayload bytes h p)).
  { intros slices Hs. rewrite nestedWrapOccursbSlices in Hnest.
    unfold fieldSlices in Hnest. rewrite Hdec in Hnest.
    assert (Hpw : positiveItemWithin bytes h p = true).
    { unfold positiveItemWithin. apply andb_true_iff.
      split; [apply Z.ltb_lt|apply Z.leb_le]; lia. }
    rewrite Hpw in Hnest. unfold itemPayload in Hs. rewrite Hs in Hnest.
    cbn [option_map existsb] in Hnest.
    apply orb_false_iff in Hnest as [_ Hnest]. exact Hnest. }
  assert (Hendok : forall final,
    snd (parentHeaderFieldWalk 0 parentHeaderFieldSchedule (itemPayload bytes h p) []) =
      walkAccept final -> EndValuesOk final).
  { intros final Hw index value Hidx Hnth.
    assert (Hcand : candidateParentHeader bytes =
                    candidateHeaderSuccess (candidateHeaderOfValues final)).
    { unfold candidateParentHeader, parentHeaderWalkEnd. rewrite Hwalk, Hw. reflexivity. }
    destruct Hidx as [-> | ->]; unfold endValueOkb; cbn [Nat.eqb].
    - change (intFieldsBefore 17) with 4%nat in Hnth.
      unfold blobGasUnalignedb in Hblob. rewrite Hcand in Hblob.
      cbn [parentBlobGas candidateHeaderOfValues] in Hblob. rewrite Hnth in Hblob.
      apply orb_false_iff in Hblob as [Hmod Hmax].
      apply negb_false_iff, Z.eqb_eq in Hmod. apply Z.ltb_ge in Hmax.
      pose proof (Z.div_mod value (2 ^ 17) ltac:(lia)) as Hdm.
      apply andb_true_iff. split; [apply Z.leb_le; lia|apply Z.eqb_eq; lia].
    - change (intFieldsBefore 18) with 5%nat in Hnth.
      unfold excessBlobGasAboveLimitb in Hexcess. rewrite Hcand in Hexcess.
      cbn [parentExcessBlobGas candidateHeaderOfValues] in Hexcess.
      rewrite Hnth in Hexcess. apply Z.ltb_ge in Hexcess. apply Z.leb_le. lia. }
  assert (Hrestok : forall rest,
    parentHeaderWalkRest parentHeaderFieldSchedule (itemPayload bytes h p) [] = Some rest ->
    sailSkipItems (List.length rest) rest = true).
  { intros rest Hr. unfold trailingItemMalformedb in Hitem.
    rewrite Hdec, Houter, Hr in Hitem. apply negb_false_iff in Hitem. exact Hitem. }
  assert (Hplen : Z.of_nat (List.length (itemPayload bytes h p)) < 2 ^ 31).
  { unfold itemPayload. rewrite firstn_length, skipn_length. lia. }
  assert (Htrace : Forall (fun field => fieldTriggerb field = false)
    (fst (parentHeaderFieldWalk 0 parentHeaderFieldSchedule (itemPayload bytes h p) []))).
  { rewrite <- Hwalk. apply traceTriggersOff; assumption. }
  destruct (walkCover parentHeaderFieldSchedule 0 (itemPayload bytes h p) [] eq_refl
    Hplen eq_refl Hnw ltac:(rewrite requiredPrefixSchedule; exact Hscan)
    Htrace Hendok Hrestok) as [Hnd|[[i Hrej] Hsail]].
  - left. rewrite (proj2 (Z.eqb_eq _ _) Heq).
    replace (0 <? p) with true by (symmetry; apply Z.ltb_lt; lia).
    exact Hnd.
  - right. split.
    + unfold candidateParentHeader, parentHeaderWalkEnd. rewrite Hwalk, Hrej. reflexivity.
    + unfold sailPureParentHeader. rewrite Hdec, (proj2 (Z.eqb_eq _ _) Heq).
      apply Hsail. split; [reflexivity|split; [reflexivity|constructor]].
Qed.

(* Plan step 2.4, M2: the candidate agrees with Sail outside the registered
   KnownBug triggers. *)
Theorem candidateParentHeader_sail (bytes : list byte) :
  headerFits bytes -> Z.of_nat (List.length bytes) < 2 ^ 31 ->
  (forall bug, List.In bug knownBugs -> parentHeaderBugTrigger bug bytes = false) ->
  parentHeaderSailAgrees bytes.
Proof.
  exact (candidateParentHeader_sail_from_cover knownBugTriggersCoverDivergences bytes).
Qed.
