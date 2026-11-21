(* Step 2.4 M1: the meaning of decodeParentHeader's success exits, from the
   histories of their return packages. Owner: compliance proof
   (hand-written).

   The chain: the outer call's record starts the walk with its values
   ([candidateWalkReachValues]); the records of calls 2 to 10 skip fields 0
   to 8; calls 11 to 13 are the inline integer fields 9 to 11, each value
   being the loop's fold fact on the stored register (x21, x22, x20). The
   reach with the three stored values and the walk's acceptance with three
   values give the candidate's header, and the stored bytes are
   parentHeaderSuccessBytes with three None records.

   Two facts the slot-1 package does not hold yet are explicit hypotheses
   (`m1x/SUCCESS.md` lists the generator data that adds them):
   - the fold fact of field 11 (x20, loop 0x039c, revealed at 0x03b0), in
     the spelling of `M1-LOOP_FACTS.md`; the package holds the x21 and x22
     folds but not this one, and does not bind x20 in its history;
   - [parentHeaderAcceptsCount bytes 3]: the walk accepts with three
     values. It stands for the success guards the call returns drop before
     the package (status half-words of calls 2 to 9, 11, 12; list bits and
     payload bounds of calls 11, 12; the "something left" checks of fields
     1 to 8; the definitions of x18 and x10 in the guard x18 = x10 at
     0x03b8). With those guards in the history the walk state itself gives
     it ([candidateNoOptionAfterTimestamp]). *)
From Coq Require Import List ZArith Lia.
From stdpp Require Import base list numbers bitvector.definitions.
Require Import EvmSailRlp.evm_rlp_types.
Require Import ZesuSsz.Automation2.Hist.
Require Import ZesuSsz.Automation2.ByteWindowFold.
Require Import ZesuSsz.Contracts.RlpDecodeItem.
Require Import ZesuSsz.Contracts.DecodeItemCallData.
Require Import ZesuSsz.Contracts.NamedEquation.
Require Import ZesuSsz.Contracts.ParentHeaderContract.
Require Import ZesuSsz.Contracts.ParentHeaderRootFacts.
Require Import ZesuSsz.Contracts.Candidates.ParentHeaderDomain.
Require Import ZesuSsz.Contracts.Candidates.ParentHeaderCandidate.
Require Import ZesuSsz.Interfaces.DecodeItem.
Require Import ZesuSsz.Contracts.ParentHeaderCandidateWalk.
Require Import ZesuSsz.Contracts.ParentHeaderSuccessFacts.
Require Import ZesuSsz.Contracts.ParentHeaderSuccessWalk.
Require Import ZesuSsz.Compliance.ParentHeaderCandidateFacts.
Require Import ZesuSsz.Compliance.ParentHeaderMeaningOfCandidate.
Require Import ZesuSsz.Compliance.ParentHeaderExitBridgeTactics.
Require ZesuSsz.Generated.DecodeParentHeader.FP301.FunctionReturnEntries.

Import ListNotations.
Open Scope Z_scope.

(* ---- The walk with its values in the registers of the histories ---- *)

Definition phVals (args : ParentHeaderArgs) (k : nat) (p l : bv 64) (acc : list Z) : Prop :=
  candidateWalkReachValues (parentHeaderInputBytes args) k
    (bv_unsigned p - bv_unsigned (parentHeaderInputPointer args)) (bv_unsigned l) acc.

Lemma phValsStart args a0 rest sp inputEnd before after :
  parentHeaderArgsWellFormed args ->
  decodeItemCallMeaning (decodeItemCallDataArgs (a0 :: parentHeaderInputPointer args :: rest)
    sp inputEnd (parentHeaderInputBytes args) before) after ->
  phVals args 0 (listWord64At0 after) (listWord64At8 after) [].
Proof.
  intros Hwf Hm.
  exact (reachValuesStart _ _ _ _ (parentHeaderWellFormedFits _ Hwf) (parentHeaderCallC1B _ _ _ _ _ _ _ _ Hm)).
Qed.

Lemma phValsSkip args k pc kind (p l : bv 64) acc a0 rest sp inputEnd before after :
  phVals args k p l acc ->
  decodeItemCallMeaning (decodeItemCallDataArgs (a0 :: p :: rest) sp inputEnd
    (take (Z.to_nat (bv_unsigned l))
      (drop (Z.to_nat (bv_unsigned p - bv_unsigned (parentHeaderInputPointer args)))
        (parentHeaderInputBytes args))) before) after ->
  nth_error parentHeaderFieldSchedule k = Some (pc, kind) ->
  parentHeaderFieldIsInteger kind = false ->
  (parentHeaderFieldIsRequired kind = true \/ bv_unsigned l <> 0) ->
  phVals args (S k) (bv_add p (listWord64At24 after)) (bv_sub l (listWord64At24 after)) acc.
Proof.
  intros Hs Hm Hk Hint Hreq.
  exact (reachValuesSkip _ _ _ _ _ _ _ _ _ _ Hk Hint Hreq Hs (parentHeaderCallC1B _ _ _ _ _ _ _ _ Hm)).
Qed.

Lemma phValsInteger args k pc kind (p l x : bv 64) acc a0 rest sp inputEnd before after :
  phVals args k p l acc ->
  decodeItemCallMeaning (decodeItemCallDataArgs (a0 :: p :: rest) sp inputEnd
    (take (Z.to_nat (bv_unsigned l))
      (drop (Z.to_nat (bv_unsigned p - bv_unsigned (parentHeaderInputPointer args)))
        (parentHeaderInputBytes args))) before) after ->
  nth_error parentHeaderFieldSchedule k = Some (pc, kind) ->
  parentHeaderFieldIsInteger kind = true ->
  parentHeaderFieldIsRequired kind = true ->
  bv_unsigned x = zesu_byte_window_fold (parentHeaderInputBytes args)
    (Z.to_nat (bv_unsigned (listWord64At0 after) - bv_unsigned (parentHeaderInputPointer args)))
    (Z.to_nat (bv_unsigned (listWord64At8 after))) ->
  phVals args (S k) (bv_add p (listWord64At24 after)) (bv_sub l (listWord64At24 after))
    (acc ++ [bv_unsigned x]).
Proof.
  intros Hs Hm Hk Hint Hreq Hx.
  exact (reachValuesInteger _ _ _ _ _ _ _ _ _ _ _ Hk Hint Hreq Hs (parentHeaderCallC1B _ _ _ _ _ _ _ _ Hm) Hx).
Qed.

(* ---- Slot 1: nothing left after field 11 (0x03b0 -> 0x03bc -> 0x0274) ---- *)

Lemma parentHeaderSlot1ExitMeaning_given (args : ParentHeaderArgs) (returnAddress : Z)
    (call13_after call10_after call_after : DecodeItemOutcome)
    (machine_x21_1 machine_x22_1 machine_x10 machine_x20_1 : bv 64) (unwritten_74 : list byte) :
  zesu_hist (FunctionReturnEntries.fp_machineReturn_slot1_ForwardA0N0_Hist args returnAddress
    call13_after call10_after call_after machine_x21_1 machine_x22_1 machine_x10) ->
  (bv_unsigned (parentHeaderReturnAddress args) = returnAddress /\ parentHeaderArgsWellFormed args) ->
  length unwritten_74 = 6%nat ->
  bv_unsigned machine_x20_1 = ZesuSsz.Automation2.ByteWindowFold.zesu_byte_window_fold
    (parentHeaderInputBytes args)
    (Z.to_nat (bv_unsigned (listWord64At0 call13_after) - bv_unsigned (parentHeaderInputPointer args)))
    (Z.to_nat (bv_unsigned (listWord64At8 call13_after))) ->
  parentHeaderAcceptsCount (parentHeaderInputBytes args) 3 ->
  parentHeaderResultMeaning args
    (FunctionReturnEntries.fp_machineReturn_slot1_ForwardA0N0_ResultBytes args returnAddress
      machine_x21_1 machine_x22_1 machine_x20_1 unwritten_74).
Proof.
  intros Hh [_ Hwf] Htail Hx20 Hcount.
  change (FunctionReturnEntries.fp_machineReturn_slot1_ForwardA0N0_ResultBytes args returnAddress
      machine_x21_1 machine_x22_1 machine_x20_1 unwritten_74)
    with (parentHeaderSuccessBytes machine_x21_1 machine_x22_1 machine_x20_1
      parentHeaderZeroRecord parentHeaderZeroRecord parentHeaderZeroRecord unwritten_74).
  apply parentHeaderMeaningOfCandidateWellFormed; [exact Hwf|].
  apply parentHeaderNoOptionResult; [|exact Htail].
  apply zesu_hist_elim in Hh.
  unfold FunctionReturnEntries.fp_machineReturn_slot1_ForwardA0N0_Hist, zesu_join_history in Hh.
  decompose [ex and] Hh. clear Hh.
  repeat match goal with H : zesu_named_eq ?x _ |- _ => apply zesu_named_eq_iff in H; subst x end.
  pose proof (phValsStart _ _ _ _ _ _ _ Hwf ltac:(eassumption)) as S0.
  pose proof (phValsSkip _ _ _ _ _ _ _ _ _ _ _ _ _ S0 ltac:(eassumption) eq_refl eq_refl (or_introl eq_refl)) as S1.
  pose proof (phValsSkip _ _ _ _ _ _ _ _ _ _ _ _ _ S1 ltac:(eassumption) eq_refl eq_refl (or_introl eq_refl)) as S2.
  pose proof (phValsSkip _ _ _ _ _ _ _ _ _ _ _ _ _ S2 ltac:(eassumption) eq_refl eq_refl (or_introl eq_refl)) as S3.
  pose proof (phValsSkip _ _ _ _ _ _ _ _ _ _ _ _ _ S3 ltac:(eassumption) eq_refl eq_refl (or_introl eq_refl)) as S4.
  pose proof (phValsSkip _ _ _ _ _ _ _ _ _ _ _ _ _ S4 ltac:(eassumption) eq_refl eq_refl (or_introl eq_refl)) as S5.
  pose proof (phValsSkip _ _ _ _ _ _ _ _ _ _ _ _ _ S5 ltac:(eassumption) eq_refl eq_refl (or_introl eq_refl)) as S6.
  pose proof (phValsSkip _ _ _ _ _ _ _ _ _ _ _ _ _ S6 ltac:(eassumption) eq_refl eq_refl (or_introl eq_refl)) as S7.
  pose proof (phValsSkip _ _ _ _ _ _ _ _ _ _ _ _ _ S7 ltac:(eassumption) eq_refl eq_refl (or_introl eq_refl)) as S8.
  pose proof (phValsSkip _ _ _ _ _ _ _ _ _ _ _ _ _ S8 ltac:(eassumption) eq_refl eq_refl (or_introl eq_refl)) as S9.
  pose proof (phValsInteger _ _ _ _ _ _ machine_x21_1 _ _ _ _ _ _ _ S9 ltac:(eassumption) eq_refl eq_refl eq_refl ltac:(eassumption)) as S10.
  pose proof (phValsInteger _ _ _ _ _ _ machine_x22_1 _ _ _ _ _ _ _ S10 ltac:(eassumption) eq_refl eq_refl eq_refl ltac:(eassumption)) as S11.
  pose proof (phValsInteger _ _ _ _ _ _ machine_x20_1 _ _ _ _ _ _ _ S11 ltac:(eassumption) eq_refl eq_refl eq_refl Hx20) as S12.
  exact (candidateNoOptionOfReach _ _ _ _ _ _ _ S12 Hcount).
Qed.
