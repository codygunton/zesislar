(* Step 2.4 M1, per-edge reason facts of the nextUint64 join 0x0270 (the nextUint64 call of field 15, 17 or 18 fails).
   Owner: compliance proof (registered in exit_meaning_modules of
   decodeParentHeader). One lemma per incoming edge: from the SOURCE block's
   generated history (`_Hist`, whole), the visible facts of that block and
   the edge's guard, the candidate rejects the input:
   `candidateParentHeader (parentHeaderInputBytes args) = candidateHeaderError`.
   The fact mentions no edge binder, so the join keeps it. Every proof is the
   same chain: the failing field's terminal (ParentHeaderCandidateFacts.v
   ph* lemmas), then the register walk back to the outer call through the
   named equations and the call records of the history. Pure lemmas only. *)
From Coq Require Import List ZArith Lia.
From stdpp Require Import base list numbers bitvector.definitions.
Require Import EvmSailRlp.evm_rlp_types.
Require Import ZesuSsz.Contracts.RlpDecodeItem.
Require Import ZesuSsz.Contracts.DecodeItemCallData.
Require Import ZesuSsz.Contracts.NamedEquation.
Require Import ZesuSsz.Contracts.NextUint64CallData.
Require Import ZesuSsz.Contracts.ParentHeaderContract.
Require Import ZesuSsz.Contracts.ParentHeaderRootFacts.
Require Import ZesuSsz.Contracts.Candidates.ParentHeaderCandidate.
Require Import ZesuSsz.Interfaces.DecodeItem.
Require Import ZesuSsz.Interfaces.NextUint64.
Require Import ZesuSsz.Contracts.ParentHeaderCandidateWalk.
Require Import ZesuSsz.Compliance.ParentHeaderCandidateFacts.
Require ZesuSsz.Generated.DecodeParentHeader.FP301.Pilot04a8Entries.
Require ZesuSsz.Generated.DecodeParentHeader.FP301.Pilot0568Entries.
Require ZesuSsz.Generated.DecodeParentHeader.FP301.Pilot059cEntries.

Import ListNotations.
Open Scope Z_scope.

(* edge 0x04a8 -> 0x0270: field 15's nextUint64 call fails *)
Lemma parentHeaderEdgeError_04a8_0270 (args : ParentHeaderArgs) (returnAddress : Z) (call16_after : DecodeItemOutcome) (call16_kept_x18 : bv 64) (call16_kept_x19 : bv 64) (call15_after : DecodeItemOutcome) (call15_kept_x18 : bv 64) (call15_kept_x19 : bv 64) (call14_after : DecodeItemOutcome) (call14_kept_x18 : bv 64) (call14_kept_x19 : bv 64) (call13_after : DecodeItemOutcome) (call13_kept_x18 : bv 64) (call13_kept_x19 : bv 64) (call10_after : DecodeItemOutcome) (call_after : DecodeItemOutcome) (call17_result : NextUint64Return) (call17_kept_x19 : bv 64) :
  (bv_unsigned (parentHeaderReturnAddress args) = returnAddress /\ parentHeaderArgsWellFormed args) ->
  zesu_named_eq call14_kept_x18 (bv_sub call13_kept_x18 (listWord64At24 call13_after)) ->
  zesu_named_eq call14_kept_x19 (bv_add call13_kept_x19 (listWord64At24 call13_after)) ->
  zesu_named_eq call15_kept_x18 (bv_sub call14_kept_x18 (listWord64At24 call14_after)) ->
  zesu_named_eq call15_kept_x19 (bv_add call14_kept_x19 (listWord64At24 call14_after)) ->
  zesu_named_eq call16_kept_x18 (bv_sub call15_kept_x18 (listWord64At24 call15_after)) ->
  zesu_named_eq call16_kept_x19 (bv_add call15_kept_x19 (listWord64At24 call15_after)) ->
  zesu_named_eq call17_kept_x19 (bv_add call16_kept_x19 (listWord64At24 call16_after)) ->
  phNextResult args (bv_add call16_kept_x19 (listWord64At24 call16_after)) (bv_sub call16_kept_x18 (listWord64At24 call16_after)) call17_result ->
  Pilot04a8Entries.fp_machineAt04a8_ForwardA0N0_Hist args returnAddress call16_after call16_kept_x18 call16_kept_x19 call15_after call15_kept_x18 call15_kept_x19 call14_after call14_kept_x18 call14_kept_x19 call13_after call13_kept_x18 call13_kept_x19 call10_after call_after ->
  bv_unsigned (bv_concat 16 (List.nth 9 (nextResultBytes call17_result) (BV 8 0)) (List.nth 8 (nextResultBytes call17_result) (BV 8 0))) <> 0 ->
  candidateParentHeader (parentHeaderInputBytes args) = candidateHeaderError.
Proof.
  intros [_ Hwf] ? ? ? ? ? ? ? (? & ? & ? & ?) Hh Hg.
  unfold Pilot04a8Entries.fp_machineAt04a8_ForwardA0N0_Hist, ZesuSsz.Automation2.Hist.zesu_join_history in Hh. decompose [ex and] Hh.
  eapply (phNextReject _ 15 _ _ (bv_add call16_kept_x19 (listWord64At24 call16_after)) (bv_sub call16_kept_x18 (listWord64At24 call16_after))); [exact Hg|eassumption|reflexivity|reflexivity|first [assumption | eapply phNamedNonzero; eassumption | apply walkRemainingNonzero; assumption]|].
  repeat first [eapply phRegsRenameP; [eassumption|] | eapply phRegsRenameL; [eassumption|]
    | eapply phRegsStart; eassumption
    | eapply phRegsAdvance; [eassumption|reflexivity|first [left; reflexivity | right; assumption | right; eapply phNamedNonzero; eassumption | right; apply walkRemainingNonzero; assumption]|]
    | eapply phRegsNext; [eassumption..|reflexivity|reflexivity|first [assumption | eapply phNamedNonzero; eassumption | apply walkRemainingNonzero; assumption]|]].
Qed.

(* edge 0x0568 -> 0x0270: field 17's nextUint64 call fails *)
Lemma parentHeaderEdgeError_0568_0270 (args : ParentHeaderArgs) (returnAddress : Z) (call18_after : DecodeItemOutcome) (call17_result : NextUint64Return) (call17_word_1_0 : bv 64) (call17_word_1_8 : bv 64) (call16_after : DecodeItemOutcome) (call16_kept_x18 : bv 64) (call16_kept_x19 : bv 64) (call15_after : DecodeItemOutcome) (call15_kept_x18 : bv 64) (call15_kept_x19 : bv 64) (call14_after : DecodeItemOutcome) (call14_kept_x18 : bv 64) (call14_kept_x19 : bv 64) (call13_after : DecodeItemOutcome) (call13_kept_x18 : bv 64) (call13_kept_x19 : bv 64) (call10_after : DecodeItemOutcome) (call_after : DecodeItemOutcome) (call19_result : NextUint64Return) (call19_kept_x19 : bv 64) (call17_kept_x19 : bv 64) :
  (bv_unsigned (parentHeaderReturnAddress args) = returnAddress /\ parentHeaderArgsWellFormed args) ->
  zesu_named_eq call14_kept_x18 (bv_sub call13_kept_x18 (listWord64At24 call13_after)) ->
  zesu_named_eq call14_kept_x19 (bv_add call13_kept_x19 (listWord64At24 call13_after)) ->
  zesu_named_eq call15_kept_x18 (bv_sub call14_kept_x18 (listWord64At24 call14_after)) ->
  zesu_named_eq call15_kept_x19 (bv_add call14_kept_x19 (listWord64At24 call14_after)) ->
  zesu_named_eq call16_kept_x18 (bv_sub call15_kept_x18 (listWord64At24 call15_after)) ->
  zesu_named_eq call16_kept_x19 (bv_add call15_kept_x19 (listWord64At24 call15_after)) ->
  zesu_named_eq call17_kept_x19 (bv_add call16_kept_x19 (listWord64At24 call16_after)) ->
  zesu_named_eq call19_kept_x19 (bv_add call17_word_1_0 (listWord64At24 call18_after)) ->
  phNextResult args (bv_add call17_word_1_0 (listWord64At24 call18_after)) (bv_sub call17_word_1_8 (listWord64At24 call18_after)) call19_result ->
  Pilot0568Entries.fp_machineAt0568_ForwardA0N0_Hist args returnAddress call18_after call17_result call17_word_1_0 call17_word_1_8 call16_after call16_kept_x18 call16_kept_x19 call15_after call15_kept_x18 call15_kept_x19 call14_after call14_kept_x18 call14_kept_x19 call13_after call13_kept_x18 call13_kept_x19 call10_after call_after ->
  bv_unsigned (bv_concat 16 (List.nth 9 (nextResultBytes call19_result) (BV 8 0)) (List.nth 8 (nextResultBytes call19_result) (BV 8 0))) <> 0 ->
  candidateParentHeader (parentHeaderInputBytes args) = candidateHeaderError.
Proof.
  intros [_ Hwf] ? ? ? ? ? ? ? ? (? & ? & ? & ?) Hh Hg.
  unfold Pilot0568Entries.fp_machineAt0568_ForwardA0N0_Hist, ZesuSsz.Automation2.Hist.zesu_join_history in Hh. decompose [ex and] Hh.
  eapply (phNextReject _ 17 _ _ (bv_add call17_word_1_0 (listWord64At24 call18_after)) (bv_sub call17_word_1_8 (listWord64At24 call18_after))); [exact Hg|eassumption|reflexivity|reflexivity|first [assumption | eapply phNamedNonzero; eassumption | apply walkRemainingNonzero; assumption]|].
  repeat first [eapply phRegsRenameP; [eassumption|] | eapply phRegsRenameL; [eassumption|]
    | eapply phRegsStart; eassumption
    | eapply phRegsAdvance; [eassumption|reflexivity|first [left; reflexivity | right; assumption | right; eapply phNamedNonzero; eassumption | right; apply walkRemainingNonzero; assumption]|]
    | eapply phRegsNext; [eassumption..|reflexivity|reflexivity|first [assumption | eapply phNamedNonzero; eassumption | apply walkRemainingNonzero; assumption]|]].
Qed.

(* edge 0x059c -> 0x0270, with the window fact the generator must add: the visible record of call 20
   (field 18) binds its slice words existentially; the lemma states them as call 19's rest words,
   which is what the slice holds after call 19 (`call20_arg_word_1_0 = call19_word_1_0`,
   `call20_arg_word_1_8 = call19_word_1_8`).
   was: edge 0x059c -> 0x0270: field 18's nextUint64 call fails *)
Lemma parentHeaderEdgeError_059c_0270 (args : ParentHeaderArgs) (returnAddress : Z) (call19_result : NextUint64Return) (call18_after : DecodeItemOutcome) (call17_result : NextUint64Return) (call17_word_1_0 : bv 64) (call16_after : DecodeItemOutcome) (call16_kept_x18 : bv 64) (call16_kept_x19 : bv 64) (call15_after : DecodeItemOutcome) (call15_kept_x18 : bv 64) (call15_kept_x19 : bv 64) (call14_after : DecodeItemOutcome) (call14_kept_x18 : bv 64) (call14_kept_x19 : bv 64) (call13_after : DecodeItemOutcome) (call13_kept_x18 : bv 64) (call13_kept_x19 : bv 64) (call10_after : DecodeItemOutcome) (call_after : DecodeItemOutcome) (call20_result : NextUint64Return) (call19_kept_x19 : bv 64) (call17_kept_x19 : bv 64) :
  (bv_unsigned (parentHeaderReturnAddress args) = returnAddress /\ parentHeaderArgsWellFormed args) ->
  zesu_named_eq call14_kept_x18 (bv_sub call13_kept_x18 (listWord64At24 call13_after)) ->
  zesu_named_eq call14_kept_x19 (bv_add call13_kept_x19 (listWord64At24 call13_after)) ->
  zesu_named_eq call15_kept_x18 (bv_sub call14_kept_x18 (listWord64At24 call14_after)) ->
  zesu_named_eq call15_kept_x19 (bv_add call14_kept_x19 (listWord64At24 call14_after)) ->
  zesu_named_eq call16_kept_x18 (bv_sub call15_kept_x18 (listWord64At24 call15_after)) ->
  zesu_named_eq call16_kept_x19 (bv_add call15_kept_x19 (listWord64At24 call15_after)) ->
  zesu_named_eq call17_kept_x19 (bv_add call16_kept_x19 (listWord64At24 call16_after)) ->
  zesu_named_eq call19_kept_x19 (bv_add call17_word_1_0 (listWord64At24 call18_after)) ->
  phNextResult args (Z_to_bv 64 (nextRestPointer call19_result)) (Z_to_bv 64 (nextRestLength call19_result))
    call20_result ->
  Pilot059cEntries.fp_machineAt059c_ForwardA0N0_Hist args returnAddress call19_result call18_after call17_result call17_word_1_0 call16_after call16_kept_x18 call16_kept_x19 call15_after call15_kept_x18 call15_kept_x19 call14_after call14_kept_x18 call14_kept_x19 call13_after call13_kept_x18 call13_kept_x19 call10_after call_after ->
  bv_unsigned (bv_concat 16 (List.nth 9 (nextResultBytes call20_result) (BV 8 0)) (List.nth 8 (nextResultBytes call20_result) (BV 8 0))) <> 0 ->
  candidateParentHeader (parentHeaderInputBytes args) = candidateHeaderError.
Proof.
  intros [_ Hwf] ? ? ? ? ? ? ? ? (? & ? & ? & ?) Hh Hg.
  unfold Pilot059cEntries.fp_machineAt059c_ForwardA0N0_Hist, ZesuSsz.Automation2.Hist.zesu_join_history in Hh. decompose [ex and] Hh.
  repeat match goal with H : ?w = Z_to_bv 64 (_ call19_result) |- _ => is_var w; subst w end.
  eapply (phNextReject _ 18 _ _ (Z_to_bv 64 (nextRestPointer call19_result)) (Z_to_bv 64 (nextRestLength call19_result))); [exact Hg|eassumption|reflexivity|reflexivity|first [assumption | eapply phNamedNonzero; eassumption | apply walkRemainingNonzero; assumption]|].
  repeat first [eapply phRegsRenameP; [eassumption|] | eapply phRegsRenameL; [eassumption|]
    | eapply phRegsStart; eassumption
    | eapply phRegsAdvance; [eassumption|reflexivity|first [left; reflexivity | right; assumption | right; eapply phNamedNonzero; eassumption | right; apply walkRemainingNonzero; assumption]|]
    | eapply phRegsNext; [first [eassumption|reflexivity]..|reflexivity|reflexivity|first [assumption | eapply phNamedNonzero; eassumption | apply walkRemainingNonzero; assumption]|]].
Qed.
