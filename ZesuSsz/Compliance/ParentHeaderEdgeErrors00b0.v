(* Step 2.4 M1, per-edge reason facts of the direct edges into the tail join 0x00b0 (outer call fails, outer item not a list, optional field 16's call fails).
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
Require ZesuSsz.Generated.DecodeParentHeader.FP301.Pilot0048Entries.
Require ZesuSsz.Generated.DecodeParentHeader.FP301.Pilot0094Entries.
Require ZesuSsz.Generated.DecodeParentHeader.FP301.Pilot04e4Entries.

Import ListNotations.
Open Scope Z_scope.

(* edge 0x0048 -> 0x00b0: the outer decodeItem call fails *)
Lemma parentHeaderEdgeError_0048_00b0 (args : ParentHeaderArgs) (returnAddress : Z) (call_after : DecodeItemOutcome) :
  (bv_unsigned (parentHeaderReturnAddress args) = returnAddress /\ parentHeaderArgsWellFormed args) ->
  Pilot0048Entries.fp_machineAt0048_ForwardA0N0_Hist args returnAddress call_after ->
  bv_unsigned (bv_concat 16 (List.nth 33 call_after (BV 8 0)) (List.nth 32 call_after (BV 8 0))) <> 0 ->
  candidateParentHeader (parentHeaderInputBytes args) = candidateHeaderError.
Proof.
  intros [_ Hwf] Hh Hg.
  unfold Pilot0048Entries.fp_machineAt0048_ForwardA0N0_Hist in Hh. decompose [ex and] Hh.
  eapply candidateOuterDecodeError; [eapply parentHeaderCallC1B; eassumption|exact Hg].
Qed.

(* edge 0x0094 -> 0x00b0: the outer item is not a list *)
Lemma parentHeaderEdgeError_0094_00b0 (args : ParentHeaderArgs) (returnAddress : Z) (call_after : DecodeItemOutcome) :
  (bv_unsigned (parentHeaderReturnAddress args) = returnAddress /\ parentHeaderArgsWellFormed args) ->
  Pilot0094Entries.fp_machineAt0094_ForwardA0N0_Hist args returnAddress call_after ->
  bv_unsigned (bv_and (bv_zero_extend 64 (List.nth 16 call_after (BV 8 0))) (BV 64 1)) = 0 ->
  candidateParentHeader (parentHeaderInputBytes args) = candidateHeaderError.
Proof.
  intros [_ Hwf] Hh Hg.
  unfold Pilot0094Entries.fp_machineAt0094_ForwardA0N0_Hist in Hh. decompose [ex and] Hh.
  eapply candidateOuterNotList; [eapply parentHeaderCallC1B; eassumption|eassumption|exact Hg].
Qed.

(* edge 0x04e4 -> 0x00b0: optional field 16's decodeItem call fails *)
Lemma parentHeaderEdgeError_04e4_00b0 (args : ParentHeaderArgs) (returnAddress : Z) (call17_result : NextUint64Return) (call17_word_1_0 : bv 64) (call17_word_1_8 : bv 64) (call16_after : DecodeItemOutcome) (call16_kept_x18 : bv 64) (call16_kept_x19 : bv 64) (call15_after : DecodeItemOutcome) (call15_kept_x18 : bv 64) (call15_kept_x19 : bv 64) (call14_after : DecodeItemOutcome) (call14_kept_x18 : bv 64) (call14_kept_x19 : bv 64) (call13_after : DecodeItemOutcome) (call13_kept_x18 : bv 64) (call13_kept_x19 : bv 64) (call10_after : DecodeItemOutcome) (call_after : DecodeItemOutcome) (call18_after : DecodeItemOutcome) (call17_kept_x19 : bv 64) :
  (bv_unsigned (parentHeaderReturnAddress args) = returnAddress /\ parentHeaderArgsWellFormed args) ->
  zesu_named_eq call14_kept_x18 (bv_sub call13_kept_x18 (listWord64At24 call13_after)) ->
  zesu_named_eq call14_kept_x19 (bv_add call13_kept_x19 (listWord64At24 call13_after)) ->
  zesu_named_eq call15_kept_x18 (bv_sub call14_kept_x18 (listWord64At24 call14_after)) ->
  zesu_named_eq call15_kept_x19 (bv_add call14_kept_x19 (listWord64At24 call14_after)) ->
  zesu_named_eq call16_kept_x18 (bv_sub call15_kept_x18 (listWord64At24 call15_after)) ->
  zesu_named_eq call16_kept_x19 (bv_add call15_kept_x19 (listWord64At24 call15_after)) ->
  zesu_named_eq call17_kept_x19 (bv_add call16_kept_x19 (listWord64At24 call16_after)) ->
  phCallMeaning args call17_word_1_0 call17_word_1_8 call18_after ->
  Pilot04e4Entries.fp_machineAt04e4_ForwardA0N0_Hist args returnAddress call17_result call17_word_1_0 call17_word_1_8 call16_after call16_kept_x18 call16_kept_x19 call15_after call15_kept_x18 call15_kept_x19 call14_after call14_kept_x18 call14_kept_x19 call13_after call13_kept_x18 call13_kept_x19 call10_after call_after ->
  bv_unsigned (bv_concat 16 (List.nth 33 call18_after (BV 8 0)) (List.nth 32 call18_after (BV 8 0))) <> 0 ->
  candidateParentHeader (parentHeaderInputBytes args) = candidateHeaderError.
Proof.
  intros [_ Hwf] ? ? ? ? ? ? ? (? & ? & ? & ? & ? & ?) Hh Hg.
  unfold Pilot04e4Entries.fp_machineAt04e4_ForwardA0N0_Hist, ZesuSsz.Automation2.Hist.zesu_join_history in Hh. decompose [ex and] Hh.
  eapply (phFieldError _ 16 _ _ call17_word_1_0 call17_word_1_8); [exact Hg|eassumption|reflexivity|first [left; reflexivity | right; assumption | right; eapply phNamedNonzero; eassumption | right; apply walkRemainingNonzero; assumption]|].
  repeat first [eapply phRegsRenameP; [eassumption|] | eapply phRegsRenameL; [eassumption|]
    | eapply phRegsStart; eassumption
    | eapply phRegsAdvance; [eassumption|reflexivity|first [left; reflexivity | right; assumption | right; eapply phNamedNonzero; eassumption | right; apply walkRemainingNonzero; assumption]|]
    | eapply phRegsNext; [eassumption..|reflexivity|reflexivity|first [assumption | eapply phNamedNonzero; eassumption | apply walkRemainingNonzero; assumption]|]].
Qed.
