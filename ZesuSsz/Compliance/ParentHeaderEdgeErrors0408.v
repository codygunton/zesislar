(* Step 2.4 M1, per-edge reason facts of the join 0x0408 (the call of optional field 12, 13 or 14 fails).
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
Require ZesuSsz.Generated.DecodeParentHeader.FP301.Pilot0400Entries.
Require ZesuSsz.Generated.DecodeParentHeader.FP301.Pilot0438Entries.
Require ZesuSsz.Generated.DecodeParentHeader.FP301.Pilot0464Entries.

Import ListNotations.
Open Scope Z_scope.

(* edge 0x0400 -> 0x0408: optional field 12's decodeItem call fails *)
Lemma parentHeaderEdgeError_0400_0408 (args : ParentHeaderArgs) (returnAddress : Z) (call13_after : DecodeItemOutcome) (call13_kept_x18 : bv 64) (call13_kept_x19 : bv 64) (call10_after : DecodeItemOutcome) (call_after : DecodeItemOutcome) (call14_after : DecodeItemOutcome) (call14_kept_x18 : bv 64) (call14_kept_x19 : bv 64) :
  (bv_unsigned (parentHeaderReturnAddress args) = returnAddress /\ parentHeaderArgsWellFormed args) ->
  zesu_named_eq call14_kept_x18 (bv_sub call13_kept_x18 (listWord64At24 call13_after)) ->
  zesu_named_eq call14_kept_x19 (bv_add call13_kept_x19 (listWord64At24 call13_after)) ->
  phCallMeaning args call14_kept_x19 call14_kept_x18 call14_after ->
  Pilot0400Entries.fp_machineAt0400_ForwardA0N0_Hist args returnAddress call13_after call13_kept_x18 call13_kept_x19 call10_after call_after ->
  bv_unsigned (bv_concat 16 (List.nth 33 call14_after (BV 8 0)) (List.nth 32 call14_after (BV 8 0))) <> 0 ->
  candidateParentHeader (parentHeaderInputBytes args) = candidateHeaderError.
Proof.
  intros [_ Hwf] ? ? (? & ? & ? & ? & ? & ?) Hh Hg.
  unfold Pilot0400Entries.fp_machineAt0400_ForwardA0N0_Hist, ZesuSsz.Automation2.Hist.zesu_join_history in Hh. decompose [ex and] Hh.
  eapply (phFieldError _ 12 _ _ call14_kept_x19 call14_kept_x18); [exact Hg|eassumption|reflexivity|first [left; reflexivity | right; assumption | right; eapply phNamedNonzero; eassumption | right; apply walkRemainingNonzero; assumption]|].
  repeat first [eapply phRegsRenameP; [eassumption|] | eapply phRegsRenameL; [eassumption|]
    | eapply phRegsStart; eassumption
    | eapply phRegsAdvance; [eassumption|reflexivity|first [left; reflexivity | right; assumption | right; eapply phNamedNonzero; eassumption | right; apply walkRemainingNonzero; assumption]|]
    | eapply phRegsNext; [eassumption..|reflexivity|reflexivity|first [assumption | eapply phNamedNonzero; eassumption | apply walkRemainingNonzero; assumption]|]].
Qed.

(* edge 0x0438 -> 0x0408: optional field 13's decodeItem call fails *)
Lemma parentHeaderEdgeError_0438_0408 (args : ParentHeaderArgs) (returnAddress : Z) (call14_after : DecodeItemOutcome) (call14_kept_x18 : bv 64) (call14_kept_x19 : bv 64) (call13_after : DecodeItemOutcome) (call13_kept_x18 : bv 64) (call13_kept_x19 : bv 64) (call10_after : DecodeItemOutcome) (call_after : DecodeItemOutcome) (call15_after : DecodeItemOutcome) (call15_kept_x18 : bv 64) (call15_kept_x19 : bv 64) :
  (bv_unsigned (parentHeaderReturnAddress args) = returnAddress /\ parentHeaderArgsWellFormed args) ->
  zesu_named_eq call14_kept_x18 (bv_sub call13_kept_x18 (listWord64At24 call13_after)) ->
  zesu_named_eq call14_kept_x19 (bv_add call13_kept_x19 (listWord64At24 call13_after)) ->
  zesu_named_eq call15_kept_x18 (bv_sub call14_kept_x18 (listWord64At24 call14_after)) ->
  zesu_named_eq call15_kept_x19 (bv_add call14_kept_x19 (listWord64At24 call14_after)) ->
  phCallMeaning args call15_kept_x19 call15_kept_x18 call15_after ->
  Pilot0438Entries.fp_machineAt0438_ForwardA0N0_Hist args returnAddress call14_after call14_kept_x18 call14_kept_x19 call13_after call13_kept_x18 call13_kept_x19 call10_after call_after ->
  bv_unsigned (bv_concat 16 (List.nth 33 call15_after (BV 8 0)) (List.nth 32 call15_after (BV 8 0))) <> 0 ->
  candidateParentHeader (parentHeaderInputBytes args) = candidateHeaderError.
Proof.
  intros [_ Hwf] ? ? ? ? (? & ? & ? & ? & ? & ?) Hh Hg.
  unfold Pilot0438Entries.fp_machineAt0438_ForwardA0N0_Hist, ZesuSsz.Automation2.Hist.zesu_join_history in Hh. decompose [ex and] Hh.
  eapply (phFieldError _ 13 _ _ call15_kept_x19 call15_kept_x18); [exact Hg|eassumption|reflexivity|first [left; reflexivity | right; assumption | right; eapply phNamedNonzero; eassumption | right; apply walkRemainingNonzero; assumption]|].
  repeat first [eapply phRegsRenameP; [eassumption|] | eapply phRegsRenameL; [eassumption|]
    | eapply phRegsStart; eassumption
    | eapply phRegsAdvance; [eassumption|reflexivity|first [left; reflexivity | right; assumption | right; eapply phNamedNonzero; eassumption | right; apply walkRemainingNonzero; assumption]|]
    | eapply phRegsNext; [eassumption..|reflexivity|reflexivity|first [assumption | eapply phNamedNonzero; eassumption | apply walkRemainingNonzero; assumption]|]].
Qed.

(* edge 0x0464 -> 0x0408: optional field 14's decodeItem call fails *)
Lemma parentHeaderEdgeError_0464_0408 (args : ParentHeaderArgs) (returnAddress : Z) (call15_after : DecodeItemOutcome) (call15_kept_x18 : bv 64) (call15_kept_x19 : bv 64) (call14_after : DecodeItemOutcome) (call14_kept_x18 : bv 64) (call14_kept_x19 : bv 64) (call13_after : DecodeItemOutcome) (call13_kept_x18 : bv 64) (call13_kept_x19 : bv 64) (call10_after : DecodeItemOutcome) (call_after : DecodeItemOutcome) (call16_after : DecodeItemOutcome) (call16_kept_x18 : bv 64) (call16_kept_x19 : bv 64) :
  (bv_unsigned (parentHeaderReturnAddress args) = returnAddress /\ parentHeaderArgsWellFormed args) ->
  zesu_named_eq call14_kept_x18 (bv_sub call13_kept_x18 (listWord64At24 call13_after)) ->
  zesu_named_eq call14_kept_x19 (bv_add call13_kept_x19 (listWord64At24 call13_after)) ->
  zesu_named_eq call15_kept_x18 (bv_sub call14_kept_x18 (listWord64At24 call14_after)) ->
  zesu_named_eq call15_kept_x19 (bv_add call14_kept_x19 (listWord64At24 call14_after)) ->
  zesu_named_eq call16_kept_x18 (bv_sub call15_kept_x18 (listWord64At24 call15_after)) ->
  zesu_named_eq call16_kept_x19 (bv_add call15_kept_x19 (listWord64At24 call15_after)) ->
  phCallMeaning args call16_kept_x19 call16_kept_x18 call16_after ->
  Pilot0464Entries.fp_machineAt0464_ForwardA0N0_Hist args returnAddress call15_after call15_kept_x18 call15_kept_x19 call14_after call14_kept_x18 call14_kept_x19 call13_after call13_kept_x18 call13_kept_x19 call10_after call_after ->
  bv_unsigned (bv_concat 16 (List.nth 33 call16_after (BV 8 0)) (List.nth 32 call16_after (BV 8 0))) <> 0 ->
  candidateParentHeader (parentHeaderInputBytes args) = candidateHeaderError.
Proof.
  intros [_ Hwf] ? ? ? ? ? ? (? & ? & ? & ? & ? & ?) Hh Hg.
  unfold Pilot0464Entries.fp_machineAt0464_ForwardA0N0_Hist, ZesuSsz.Automation2.Hist.zesu_join_history in Hh. decompose [ex and] Hh.
  eapply (phFieldError _ 14 _ _ call16_kept_x19 call16_kept_x18); [exact Hg|eassumption|reflexivity|first [left; reflexivity | right; assumption | right; eapply phNamedNonzero; eassumption | right; apply walkRemainingNonzero; assumption]|].
  repeat first [eapply phRegsRenameP; [eassumption|] | eapply phRegsRenameL; [eassumption|]
    | eapply phRegsStart; eassumption
    | eapply phRegsAdvance; [eassumption|reflexivity|first [left; reflexivity | right; assumption | right; eapply phNamedNonzero; eassumption | right; apply walkRemainingNonzero; assumption]|]
    | eapply phRegsNext; [eassumption..|reflexivity|reflexivity|first [assumption | eapply phNamedNonzero; eassumption | apply walkRemainingNonzero; assumption]|]].
Qed.
