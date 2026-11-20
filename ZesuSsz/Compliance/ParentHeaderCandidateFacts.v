(* Step 2.4 M1 (machine implies candidate) against the generated histories
   of decodeParentHeader. Owner: compliance proof. Each lemma takes the
   history of a block (the generated `_Hist` proposition, opened from
   `zesu_hist` by `zesu_hist_elim`), the visible facts it needs and the
   edge guard, and proves the candidate fact by a chain of the step lemmas
   of ZesuSsz.Compliance.ParentHeaderCandidateWalk.

   This module is decodeParentHeader's entry of `exit_meaning_modules` in
   ZesuSsz/Contracts/proved_functions.json: the one place where
   decodeParentHeader may use decodeItemCallMeaningLink and
   nextUint64CallResultLink. It holds pure lemmas only (no tactic, no hint,
   no automation umbrella). *)
From Coq Require Import List ZArith Lia.
From stdpp Require Import base list numbers bitvector.definitions.
Require Import EvmSailRlp.evm_rlp_types.
Require Import ZesuSsz.Contracts.RlpDecodeItem.
Require Import ZesuSsz.Contracts.RlpDecodeItemContract.
Require Import ZesuSsz.Contracts.DecodeItemCallData.
Require Import ZesuSsz.Contracts.NamedEquation.
Require Import ZesuSsz.Contracts.NextUint64CallData.
Require Import ZesuSsz.Contracts.ParentHeaderContract.
Require Import ZesuSsz.Contracts.ParentHeaderRootFacts.
Require Import ZesuSsz.Contracts.Candidates.ParentHeaderDomain.
Require Import ZesuSsz.Contracts.Candidates.ParentHeaderCandidate.
Require Import ZesuSsz.Interfaces.DecodeItem.
Require Import ZesuSsz.Interfaces.NextUint64.
Require Import ZesuSsz.Contracts.ParentHeaderCandidateWalk.
Require ZesuSsz.Generated.DecodeParentHeader.FP301.Pilot0060Entries.
Require ZesuSsz.Generated.DecodeParentHeader.FP301.Pilot00a0Entries.
Require ZesuSsz.Generated.DecodeParentHeader.FP301.Pilot0110Entries.

Import ListNotations.
Open Scope Z_scope.

(* ---- Call records to the contract-level results ---- *)

Lemma parentHeaderCallC1B a0 a1 rest sp inputEnd input before after :
  decodeItemCallMeaning (decodeItemCallDataArgs (a0 :: a1 :: rest) sp inputEnd input before) after ->
  C1BResult (bv_unsigned a1) input before after.
Proof. intros H. exact (proj1 (decodeItemCallMeaningLink _ _ H)). Qed.

Lemma parentHeaderNextUint64Root call ret :
  nextUint64CallResult call ret -> nextUint64RootResult call ret.
Proof. exact (nextUint64CallResultLink call ret). Qed.

Lemma parentHeaderWellFormedFits args :
  parentHeaderArgsWellFormed args -> headerFits (parentHeaderInputBytes args).
Proof. intros H. repeat apply proj2 in H. exact H. Qed.

Lemma parentHeaderWellFormedError80 args :
  parentHeaderArgsWellFormed args -> parentHeaderError80 (parentHeaderMemcpySourceBefore args).
Proof. intros (_ & _ & _ & _ & H & _). exact H. Qed.

(* ---- The walk in the registers of the generated histories ----
   [phRegs args k p l]: before field k the code's cursor register is [p] and
   its length register is [l], or the candidate already rejects. A history
   reaches it backwards: a register named by a [zesu_named_eq] is renamed to
   its definition, a definition [p + consumed] / [l - consumed] of a field
   call is one step back over that call's record ([phRegsAdvance]), the rest
   words of a nextUint64 call are one step back over its record
   ([phRegsNext]), and the outer call's payload words are the start. *)

Definition phRegs (args : ParentHeaderArgs) (k : nat) (p l : bv 64) : Prop :=
  candidateWalkReach (parentHeaderInputBytes args) k
    (bv_unsigned p - bv_unsigned (parentHeaderInputPointer args)) (bv_unsigned l).

(* The record of a field call on the window [p, p + l) as the visible facts
   of its return site state it, without the domain conjunct. *)
Definition phCallMeaning (args : ParentHeaderArgs) (p l : bv 64) (after : DecodeItemOutcome) : Prop :=
  exists a0 rest sp inputEnd before,
    decodeItemCallMeaning (decodeItemCallDataArgs (a0 :: p :: rest) sp inputEnd
      (take (Z.to_nat (bv_unsigned l))
        (drop (Z.to_nat (bv_unsigned p - bv_unsigned (parentHeaderInputPointer args)))
          (parentHeaderInputBytes args))) before) after.

Definition phNextResult (args : ParentHeaderArgs) (p l : bv 64) (ret : NextUint64Return) : Prop :=
  exists argv sp inputEnd,
    nextUint64CallResult (nextUint64Base (nextUint64CallDataArgs argv sp p inputEnd
      (take (Z.to_nat (bv_unsigned l))
        (drop (Z.to_nat (bv_unsigned p - bv_unsigned (parentHeaderInputPointer args)))
          (parentHeaderInputBytes args))))) ret.

Lemma phRegsStart args a0 rest sp inputEnd before after :
  decodeItemCallMeaning (decodeItemCallDataArgs (a0 :: parentHeaderInputPointer args :: rest)
    sp inputEnd (parentHeaderInputBytes args) before) after ->
  parentHeaderArgsWellFormed args ->
  phRegs args 0 (listWord64At0 after) (listWord64At8 after).
Proof.
  intros Hm Hwf.
  exact (candidateReachStart _ _ _ _ (parentHeaderWellFormedFits _ Hwf) (parentHeaderCallC1B _ _ _ _ _ _ _ _ Hm)).
Qed.

Lemma phRegsRenameP args k (p p' l : bv 64) :
  zesu_named_eq p p' -> phRegs args k p' l -> phRegs args k p l.
Proof. intros [->] H. exact H. Qed.

Lemma phRegsRenameL args k (p l l' : bv 64) :
  zesu_named_eq l l' -> phRegs args k p l' -> phRegs args k p l.
Proof. intros [->] H. exact H. Qed.

Lemma phNamedNonzero (l l0 w : bv 64) :
  zesu_named_eq l (bv_sub l0 w) -> bv_unsigned l0 <> bv_unsigned w -> bv_unsigned l <> 0.
Proof. intros [->]. apply walkRemainingNonzero. Qed.

Lemma phRegsAdvance args k pc kind (p l : bv 64) a0 rest sp inputEnd before after :
  decodeItemCallMeaning (decodeItemCallDataArgs (a0 :: p :: rest) sp inputEnd
    (take (Z.to_nat (bv_unsigned l))
      (drop (Z.to_nat (bv_unsigned p - bv_unsigned (parentHeaderInputPointer args)))
        (parentHeaderInputBytes args))) before) after ->
  nth_error parentHeaderFieldSchedule k = Some (pc, kind) ->
  (parentHeaderFieldIsRequired kind = true \/ bv_unsigned l <> 0) ->
  phRegs args k p l ->
  phRegs args (S k) (bv_add p (listWord64At24 after)) (bv_sub l (listWord64At24 after)).
Proof.
  intros Hm Hk Hreq Hs.
  exact (candidateReachAdvance _ _ _ _ _ _ _ _ _ Hk Hreq Hs (parentHeaderCallC1B _ _ _ _ _ _ _ _ Hm)).
Qed.

Lemma phRegsNext args k pc kind (p l w0 w8 : bv 64) argv sp inputEnd ret :
  w0 = Z_to_bv 64 (nextRestPointer ret) ->
  w8 = Z_to_bv 64 (nextRestLength ret) ->
  nextUint64CallResult (nextUint64Base (nextUint64CallDataArgs argv sp p inputEnd
    (take (Z.to_nat (bv_unsigned l))
      (drop (Z.to_nat (bv_unsigned p - bv_unsigned (parentHeaderInputPointer args)))
        (parentHeaderInputBytes args))))) ret ->
  bv_unsigned (bv_concat 16 (List.nth 9 (nextResultBytes ret) (BV 8 0))
    (List.nth 8 (nextResultBytes ret) (BV 8 0))) = 0 ->
  nth_error parentHeaderFieldSchedule k = Some (pc, kind) ->
  parentHeaderFieldIsInteger kind = true ->
  bv_unsigned l <> 0 ->
  phRegs args k p l ->
  phRegs args (S k) w0 w8.
Proof.
  intros H0 H8 Hr Hok Hk Hkind Hl Hs.
  unfold phRegs in *.
  eapply (candidateReachNextUint64 _ _ _ _ (parentHeaderInputPointer args) p l w0 w8 _ ret
    Hk Hkind Hl Hs _ _ (parentHeaderNextUint64Root _ _ Hr) Hok H0 H8).
  Unshelve. all: reflexivity.
Qed.

(* ---- Error terminals in the registers ---- *)

Lemma phFieldError args k pc kind (p l : bv 64) a0 rest sp inputEnd before after :
  bv_unsigned (bv_concat 16 (List.nth 33 after (BV 8 0)) (List.nth 32 after (BV 8 0))) <> 0 ->
  decodeItemCallMeaning (decodeItemCallDataArgs (a0 :: p :: rest) sp inputEnd
    (take (Z.to_nat (bv_unsigned l))
      (drop (Z.to_nat (bv_unsigned p - bv_unsigned (parentHeaderInputPointer args)))
        (parentHeaderInputBytes args))) before) after ->
  nth_error parentHeaderFieldSchedule k = Some (pc, kind) ->
  (parentHeaderFieldIsRequired kind = true \/ bv_unsigned l <> 0) ->
  phRegs args k p l ->
  candidateParentHeader (parentHeaderInputBytes args) = candidateHeaderError.
Proof.
  intros Hbad Hm Hk Hreq Hs.
  exact (candidateReachFieldError _ _ _ _ _ _ _ _ _ Hk Hreq Hs (parentHeaderCallC1B _ _ _ _ _ _ _ _ Hm) Hbad).
Qed.

(* A field call consumed everything left and the next field is required. *)
Lemma phMissingNext args k pc kind (p l : bv 64) after :
  l = listWord64At24 after ->
  nth_error parentHeaderFieldSchedule (S k) = Some (pc, kind) ->
  parentHeaderFieldIsRequired kind = true ->
  phRegs args (S k) (bv_add p (listWord64At24 after)) (bv_sub l (listWord64At24 after)) ->
  candidateParentHeader (parentHeaderInputBytes args) = candidateHeaderError.
Proof.
  intros -> Hk Hreq Hs. unfold phRegs in Hs.
  replace (bv_unsigned (bv_sub (listWord64At24 after) (listWord64At24 after))) with 0 in Hs
    by (rewrite bv_sub_unsigned, Z.sub_diag; reflexivity).
  exact (candidateReachMissing _ _ _ _ _ Hk Hreq Hs).
Qed.

Lemma phIntegerReject args k pc kind (p l : bv 64) a0 rest sp inputEnd before after :
  (bv_unsigned (bv_and (bv_zero_extend 64 (List.nth 16 after (BV 8 0))) (BV 64 1)) <> 0 \/
   8 < bv_unsigned (listWord64At8 after)) ->
  bv_unsigned (bv_concat 16 (List.nth 33 after (BV 8 0)) (List.nth 32 after (BV 8 0))) = 0 ->
  decodeItemCallMeaning (decodeItemCallDataArgs (a0 :: p :: rest) sp inputEnd
    (take (Z.to_nat (bv_unsigned l))
      (drop (Z.to_nat (bv_unsigned p - bv_unsigned (parentHeaderInputPointer args)))
        (parentHeaderInputBytes args))) before) after ->
  nth_error parentHeaderFieldSchedule k = Some (pc, kind) ->
  parentHeaderFieldIsInteger kind = true ->
  parentHeaderFieldIsRequired kind = true ->
  phRegs args k p l ->
  candidateParentHeader (parentHeaderInputBytes args) = candidateHeaderError.
Proof.
  intros Hbad Hok Hm Hk Hkind Hreq Hs.
  exact (candidateReachIntegerReject _ _ _ _ _ _ _ _ _ Hk Hkind Hreq Hs
    (parentHeaderCallC1B _ _ _ _ _ _ _ _ Hm) Hok Hbad).
Qed.

Lemma phNextReject args k pc kind (p l : bv 64) argv sp inputEnd ret :
  bv_unsigned (bv_concat 16 (List.nth 9 (nextResultBytes ret) (BV 8 0))
    (List.nth 8 (nextResultBytes ret) (BV 8 0))) <> 0 ->
  nextUint64CallResult (nextUint64Base (nextUint64CallDataArgs argv sp p inputEnd
    (take (Z.to_nat (bv_unsigned l))
      (drop (Z.to_nat (bv_unsigned p - bv_unsigned (parentHeaderInputPointer args)))
        (parentHeaderInputBytes args))))) ret ->
  nth_error parentHeaderFieldSchedule k = Some (pc, kind) ->
  parentHeaderFieldIsInteger kind = true ->
  bv_unsigned l <> 0 ->
  phRegs args k p l ->
  candidateParentHeader (parentHeaderInputBytes args) = candidateHeaderError.
Proof.
  intros Hbad Hr Hk Hkind Hl Hs.
  unfold phRegs in *.
  eapply (candidateReachNextUint64Reject _ _ _ _ _ _ _ ret Hk Hkind Hl Hs _
    (parentHeaderNextUint64Root _ _ Hr) Hbad).
  Unshelve. reflexivity.
Qed.

(* ---- Error exit: the outer list is empty (edge 0x0060 -> 0x00a8) ----
   Block 0x0060 holds call 1's record (the whole input), its success
   status and the list flag; the edge is `beq x18, zero` at 0x0064, x18 the
   payload length (word 8 of call 1's output). The tail join 0x00a8 then
   copies the constant error union (parentHeaderMemcpySourceBefore). *)
Lemma parentHeaderCandidate_0060_00a8 (args : ParentHeaderArgs) (returnAddress : Z)
    (call_after : DecodeItemOutcome) :
  (bv_unsigned (parentHeaderReturnAddress args) = returnAddress /\ parentHeaderArgsWellFormed args) ->
  Pilot0060Entries.fp_machineAt0060_ForwardA0N0_Hist args returnAddress call_after ->
  bv_unsigned (listWord64At8 call_after) = 0 ->
  parentHeaderCandidateResult (parentHeaderInputBytes args) (parentHeaderMemcpySourceBefore args).
Proof.
  intros [_ Hwf] Hh Hguard.
  apply parentHeaderCandidateResultError; [|exact (parentHeaderWellFormedError80 _ Hwf)].
  unfold Pilot0060Entries.fp_machineAt0060_ForwardA0N0_Hist in Hh.
  decompose [ex and] Hh.
  eapply candidateOuterEmpty; [eapply parentHeaderCallC1B; eassumption | eassumption | exact Hguard].
Qed.

(* ---- Error exit: the first field consumes the whole payload (edge 0x00a0 -> 0x00a8) ----
   Block 0x00a0 holds call 1's record, call 2's record (field 0 on the
   payload window), the named equations of call 2's window registers and
   both success statuses; the edge is `bne x18, x10` not taken at 0x00a4:
   the consumed length of call 2 equals its window length, so nothing is
   left before the required field 1. *)
Lemma parentHeaderCandidate_00a0_00a8 (args : ParentHeaderArgs) (returnAddress : Z)
    (call2_after : DecodeItemOutcome) (call2_kept_x18 call2_kept_x19 : bv 64)
    (call_after : DecodeItemOutcome) :
  (bv_unsigned (parentHeaderReturnAddress args) = returnAddress /\ parentHeaderArgsWellFormed args) ->
  Pilot00a0Entries.fp_machineAt00a0_ForwardA0N0_Hist args returnAddress call2_after
    call2_kept_x18 call2_kept_x19 call_after ->
  call2_kept_x18 = listWord64At24 call2_after ->
  parentHeaderCandidateResult (parentHeaderInputBytes args) (parentHeaderMemcpySourceBefore args).
Proof.
  intros [_ Hwf] Hh Hguard.
  apply parentHeaderCandidateResultError; [|exact (parentHeaderWellFormedError80 _ Hwf)].
  unfold Pilot00a0Entries.fp_machineAt00a0_ForwardA0N0_Hist in Hh.
  decompose [ex and] Hh.
  repeat match goal with H : zesu_named_eq _ _ |- _ => apply zesu_named_eq_iff in H end.
  assert (Hs0 : candidateWalkState (parentHeaderInputBytes args) 0
    (bv_unsigned (listWord64At0 call_after) - bv_unsigned (parentHeaderInputPointer args))
    (bv_unsigned (listWord64At8 call_after)) []).
  { eapply candidateWalkStart; [exact (parentHeaderWellFormedFits _ Hwf)
      | eapply parentHeaderCallC1B; eassumption | eassumption | eassumption | eassumption]. }
  match goal with Hx : call2_kept_x18 = _ |- _ => rewrite <- Hx in Hs0 end.
  match goal with Hx : call2_kept_x19 = _ |- _ => rewrite <- Hx in Hs0 end.
  assert (Hl2 : bv_unsigned call2_kept_x18 <> 0)
    by (match goal with Hx : call2_kept_x18 = _ |- _ => rewrite Hx end; assumption).
  assert (Hs1 : candidateWalkState (parentHeaderInputBytes args) 1
    (bv_unsigned (bv_add call2_kept_x19 (listWord64At24 call2_after)) -
       bv_unsigned (parentHeaderInputPointer args))
    (bv_unsigned (bv_sub call2_kept_x18 (listWord64At24 call2_after))) []).
  { eapply candidateWalkSkipMachine; [reflexivity | reflexivity | exact Hs0 | exact Hl2
      | eapply parentHeaderCallC1B; eassumption | eassumption]. }
  rewrite <- Hguard in Hs1.
  replace (bv_unsigned (bv_sub call2_kept_x18 call2_kept_x18)) with 0 in Hs1
    by (rewrite bv_sub_unsigned, Z.sub_diag; reflexivity).
  exact (candidateWalkMissing _ 1 _ _ _ _ eq_refl eq_refl Hs1).
Qed.

(* ---- Success prefix: after the outer item and fields 0 and 1 (block 0x0110) ----
   Block 0x0110 is the return site of call 3 (field 1) after its success
   check. Its history holds the three call records, the window facts, the
   success statuses, the list flag, the non-empty payload and call 2's
   consumed length differing from its window (the edge 0x00a0 -> 0x00ec);
   its visible facts are the named equations of the window registers of
   calls 2 and 3. The walk then stands before field 2 at the registers the
   code computes at 0x0118 for call 4 (x19 + consumed, x18 - consumed). *)
Lemma parentHeaderCandidateWalk_0110 (args : ParentHeaderArgs) (returnAddress : Z)
    (call3_after : DecodeItemOutcome) (call3_kept_x18 call3_kept_x19 : bv 64)
    (call2_after : DecodeItemOutcome) (call2_kept_x18 call2_kept_x19 : bv 64)
    (call_after : DecodeItemOutcome) :
  (bv_unsigned (parentHeaderReturnAddress args) = returnAddress /\ parentHeaderArgsWellFormed args) ->
  zesu_named_eq call2_kept_x18 (listWord64At8 call_after) ->
  zesu_named_eq call2_kept_x19 (listWord64At0 call_after) ->
  zesu_named_eq call3_kept_x18 (bv_sub call2_kept_x18 (listWord64At24 call2_after)) ->
  zesu_named_eq call3_kept_x19 (bv_add call2_kept_x19 (listWord64At24 call2_after)) ->
  Pilot0110Entries.fp_machineAt0110_ForwardA0N0_Hist args returnAddress call3_after
    call3_kept_x18 call3_kept_x19 call2_after call2_kept_x18 call2_kept_x19 call_after ->
  candidateWalkState (parentHeaderInputBytes args) 2
    (bv_unsigned (bv_add call3_kept_x19 (listWord64At24 call3_after)) -
       bv_unsigned (parentHeaderInputPointer args))
    (bv_unsigned (bv_sub call3_kept_x18 (listWord64At24 call3_after))) [].
Proof.
  intros [_ Hwf] Hx18 Hx19 Hy18 Hy19 Hh.
  apply zesu_named_eq_iff in Hx18, Hx19, Hy18, Hy19.
  unfold Pilot0110Entries.fp_machineAt0110_ForwardA0N0_Hist in Hh.
  decompose [ex and] Hh.
  assert (Hs0 : candidateWalkState (parentHeaderInputBytes args) 0
    (bv_unsigned (listWord64At0 call_after) - bv_unsigned (parentHeaderInputPointer args))
    (bv_unsigned (listWord64At8 call_after)) []).
  { eapply candidateWalkStart; [exact (parentHeaderWellFormedFits _ Hwf)
      | eapply parentHeaderCallC1B; eassumption | eassumption | eassumption | eassumption]. }
  rewrite <- Hx18, <- Hx19 in Hs0.
  assert (Hl2 : bv_unsigned call2_kept_x18 <> 0) by (rewrite Hx18; assumption).
  assert (Hs1 : candidateWalkState (parentHeaderInputBytes args) 1
    (bv_unsigned (bv_add call2_kept_x19 (listWord64At24 call2_after)) -
       bv_unsigned (parentHeaderInputPointer args))
    (bv_unsigned (bv_sub call2_kept_x18 (listWord64At24 call2_after))) []).
  { eapply candidateWalkSkipMachine; [reflexivity | reflexivity | exact Hs0 | exact Hl2
      | eapply parentHeaderCallC1B; eassumption | eassumption]. }
  rewrite <- Hy18, <- Hy19 in Hs1.
  assert (Hl3 : bv_unsigned call3_kept_x18 <> 0)
    by (rewrite Hy18; apply walkRemainingNonzero; assumption).
  eapply candidateWalkSkipMachine; [reflexivity | reflexivity | exact Hs1 | exact Hl3
    | eapply parentHeaderCallC1B; eassumption | eassumption].
Qed.
