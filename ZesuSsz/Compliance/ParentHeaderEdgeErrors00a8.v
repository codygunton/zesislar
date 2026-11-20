(* Step 2.4 M1, per-edge reason facts of the required-field-missing join 0x00a8 (outer payload empty, or a skipped field 0 to 7 consumes everything left before a required field).
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
Require ZesuSsz.Generated.DecodeParentHeader.FP301.Pilot0060Entries.
Require ZesuSsz.Generated.DecodeParentHeader.FP301.Pilot00a0Entries.
Require ZesuSsz.Generated.DecodeParentHeader.FP301.Pilot0110Entries.
Require ZesuSsz.Generated.DecodeParentHeader.FP301.Pilot013cEntries.
Require ZesuSsz.Generated.DecodeParentHeader.FP301.Pilot0168Entries.
Require ZesuSsz.Generated.DecodeParentHeader.FP301.Pilot0194Entries.
Require ZesuSsz.Generated.DecodeParentHeader.FP301.Pilot01c0Entries.
Require ZesuSsz.Generated.DecodeParentHeader.FP301.Pilot01ecEntries.
Require ZesuSsz.Generated.DecodeParentHeader.FP301.Pilot0218Entries.

Import ListNotations.
Open Scope Z_scope.

(* edge 0x0060 -> 0x00a8: the outer list's payload is empty *)
Lemma parentHeaderEdgeError_0060_00a8 (args : ParentHeaderArgs) (returnAddress : Z) (call_after : DecodeItemOutcome) :
  (bv_unsigned (parentHeaderReturnAddress args) = returnAddress /\ parentHeaderArgsWellFormed args) ->
  Pilot0060Entries.fp_machineAt0060_ForwardA0N0_Hist args returnAddress call_after ->
  bv_unsigned (listWord64At8 call_after) = 0 ->
  candidateParentHeader (parentHeaderInputBytes args) = candidateHeaderError.
Proof.
  intros [_ Hwf] Hh Hg.
  unfold Pilot0060Entries.fp_machineAt0060_ForwardA0N0_Hist in Hh. decompose [ex and] Hh.
  eapply candidateOuterEmpty; [eapply parentHeaderCallC1B; eassumption|eassumption|exact Hg].
Qed.

(* edge 0x00a0 -> 0x00a8: field 0 consumes everything left, required field 1 is missing *)
Lemma parentHeaderEdgeError_00a0_00a8 (args : ParentHeaderArgs) (returnAddress : Z) (call2_after : DecodeItemOutcome) (call2_kept_x18 : bv 64) (call2_kept_x19 : bv 64) (call_after : DecodeItemOutcome) :
  (bv_unsigned (parentHeaderReturnAddress args) = returnAddress /\ parentHeaderArgsWellFormed args) ->
  Pilot00a0Entries.fp_machineAt00a0_ForwardA0N0_Hist args returnAddress call2_after call2_kept_x18 call2_kept_x19 call_after ->
  call2_kept_x18 = listWord64At24 call2_after ->
  candidateParentHeader (parentHeaderInputBytes args) = candidateHeaderError.
Proof.
  intros [_ Hwf] Hh Hg.
  unfold Pilot00a0Entries.fp_machineAt00a0_ForwardA0N0_Hist in Hh. decompose [ex and] Hh.
  eapply (phMissingNext _ 0 _ _ call2_kept_x19 call2_kept_x18 call2_after); [exact Hg|reflexivity|reflexivity|].
  repeat first [eapply phRegsRenameP; [eassumption|] | eapply phRegsRenameL; [eassumption|]
    | eapply phRegsStart; eassumption
    | eapply phRegsAdvance; [eassumption|reflexivity|first [left; reflexivity | right; assumption | right; eapply phNamedNonzero; eassumption | right; apply walkRemainingNonzero; assumption]|]
    | eapply phRegsNext; [eassumption..|reflexivity|reflexivity|first [assumption | eapply phNamedNonzero; eassumption | apply walkRemainingNonzero; assumption]|]].
Qed.

(* edge 0x0110 -> 0x00a8: field 1 consumes everything left, required field 2 is missing *)
Lemma parentHeaderEdgeError_0110_00a8 (args : ParentHeaderArgs) (returnAddress : Z) (call3_after : DecodeItemOutcome) (call3_kept_x18 : bv 64) (call3_kept_x19 : bv 64) (call2_after : DecodeItemOutcome) (call2_kept_x18 : bv 64) (call2_kept_x19 : bv 64) (call_after : DecodeItemOutcome) :
  (bv_unsigned (parentHeaderReturnAddress args) = returnAddress /\ parentHeaderArgsWellFormed args) ->
  zesu_named_eq call2_kept_x18 (listWord64At8 call_after) ->
  zesu_named_eq call2_kept_x19 (listWord64At0 call_after) ->
  zesu_named_eq call3_kept_x18 (bv_sub call2_kept_x18 (listWord64At24 call2_after)) ->
  zesu_named_eq call3_kept_x19 (bv_add call2_kept_x19 (listWord64At24 call2_after)) ->
  Pilot0110Entries.fp_machineAt0110_ForwardA0N0_Hist args returnAddress call3_after call3_kept_x18 call3_kept_x19 call2_after call2_kept_x18 call2_kept_x19 call_after ->
  call3_kept_x18 = listWord64At24 call3_after ->
  candidateParentHeader (parentHeaderInputBytes args) = candidateHeaderError.
Proof.
  intros [_ Hwf] ? ? ? ? Hh Hg.
  unfold Pilot0110Entries.fp_machineAt0110_ForwardA0N0_Hist in Hh. decompose [ex and] Hh.
  eapply (phMissingNext _ 1 _ _ call3_kept_x19 call3_kept_x18 call3_after); [exact Hg|reflexivity|reflexivity|].
  repeat first [eapply phRegsRenameP; [eassumption|] | eapply phRegsRenameL; [eassumption|]
    | eapply phRegsStart; eassumption
    | eapply phRegsAdvance; [eassumption|reflexivity|first [left; reflexivity | right; assumption | right; eapply phNamedNonzero; eassumption | right; apply walkRemainingNonzero; assumption]|]
    | eapply phRegsNext; [eassumption..|reflexivity|reflexivity|first [assumption | eapply phNamedNonzero; eassumption | apply walkRemainingNonzero; assumption]|]].
Qed.

(* edge 0x013c -> 0x00a8: field 2 consumes everything left, required field 3 is missing *)
Lemma parentHeaderEdgeError_013c_00a8 (args : ParentHeaderArgs) (returnAddress : Z) (call4_after : DecodeItemOutcome) (call4_kept_x18 : bv 64) (call4_kept_x19 : bv 64) (call3_after : DecodeItemOutcome) (call3_kept_x18 : bv 64) (call3_kept_x19 : bv 64) (call2_after : DecodeItemOutcome) (call2_kept_x18 : bv 64) (call2_kept_x19 : bv 64) (call_after : DecodeItemOutcome) :
  (bv_unsigned (parentHeaderReturnAddress args) = returnAddress /\ parentHeaderArgsWellFormed args) ->
  zesu_named_eq call2_kept_x18 (listWord64At8 call_after) ->
  zesu_named_eq call2_kept_x19 (listWord64At0 call_after) ->
  zesu_named_eq call3_kept_x18 (bv_sub call2_kept_x18 (listWord64At24 call2_after)) ->
  zesu_named_eq call3_kept_x19 (bv_add call2_kept_x19 (listWord64At24 call2_after)) ->
  zesu_named_eq call4_kept_x18 (bv_sub call3_kept_x18 (listWord64At24 call3_after)) ->
  zesu_named_eq call4_kept_x19 (bv_add call3_kept_x19 (listWord64At24 call3_after)) ->
  Pilot013cEntries.fp_machineAt013c_ForwardA0N0_Hist args returnAddress call4_after call4_kept_x18 call4_kept_x19 call3_after call3_kept_x18 call3_kept_x19 call2_after call2_kept_x18 call2_kept_x19 call_after ->
  call4_kept_x18 = listWord64At24 call4_after ->
  candidateParentHeader (parentHeaderInputBytes args) = candidateHeaderError.
Proof.
  intros [_ Hwf] ? ? ? ? ? ? Hh Hg.
  unfold Pilot013cEntries.fp_machineAt013c_ForwardA0N0_Hist in Hh. decompose [ex and] Hh.
  eapply (phMissingNext _ 2 _ _ call4_kept_x19 call4_kept_x18 call4_after); [exact Hg|reflexivity|reflexivity|].
  repeat first [eapply phRegsRenameP; [eassumption|] | eapply phRegsRenameL; [eassumption|]
    | eapply phRegsStart; eassumption
    | eapply phRegsAdvance; [eassumption|reflexivity|first [left; reflexivity | right; assumption | right; eapply phNamedNonzero; eassumption | right; apply walkRemainingNonzero; assumption]|]
    | eapply phRegsNext; [eassumption..|reflexivity|reflexivity|first [assumption | eapply phNamedNonzero; eassumption | apply walkRemainingNonzero; assumption]|]].
Qed.

(* edge 0x0168 -> 0x00a8: field 3 consumes everything left, required field 4 is missing *)
Lemma parentHeaderEdgeError_0168_00a8 (args : ParentHeaderArgs) (returnAddress : Z) (call5_after : DecodeItemOutcome) (call5_kept_x18 : bv 64) (call5_kept_x19 : bv 64) (call4_after : DecodeItemOutcome) (call4_kept_x18 : bv 64) (call4_kept_x19 : bv 64) (call3_after : DecodeItemOutcome) (call3_kept_x18 : bv 64) (call3_kept_x19 : bv 64) (call2_after : DecodeItemOutcome) (call2_kept_x18 : bv 64) (call2_kept_x19 : bv 64) (call_after : DecodeItemOutcome) :
  (bv_unsigned (parentHeaderReturnAddress args) = returnAddress /\ parentHeaderArgsWellFormed args) ->
  zesu_named_eq call2_kept_x18 (listWord64At8 call_after) ->
  zesu_named_eq call2_kept_x19 (listWord64At0 call_after) ->
  zesu_named_eq call3_kept_x18 (bv_sub call2_kept_x18 (listWord64At24 call2_after)) ->
  zesu_named_eq call3_kept_x19 (bv_add call2_kept_x19 (listWord64At24 call2_after)) ->
  zesu_named_eq call4_kept_x18 (bv_sub call3_kept_x18 (listWord64At24 call3_after)) ->
  zesu_named_eq call4_kept_x19 (bv_add call3_kept_x19 (listWord64At24 call3_after)) ->
  zesu_named_eq call5_kept_x18 (bv_sub call4_kept_x18 (listWord64At24 call4_after)) ->
  zesu_named_eq call5_kept_x19 (bv_add call4_kept_x19 (listWord64At24 call4_after)) ->
  Pilot0168Entries.fp_machineAt0168_ForwardA0N0_Hist args returnAddress call5_after call5_kept_x18 call5_kept_x19 call4_after call4_kept_x18 call4_kept_x19 call3_after call3_kept_x18 call3_kept_x19 call2_after call2_kept_x18 call2_kept_x19 call_after ->
  call5_kept_x18 = listWord64At24 call5_after ->
  candidateParentHeader (parentHeaderInputBytes args) = candidateHeaderError.
Proof.
  intros [_ Hwf] ? ? ? ? ? ? ? ? Hh Hg.
  unfold Pilot0168Entries.fp_machineAt0168_ForwardA0N0_Hist in Hh. decompose [ex and] Hh.
  eapply (phMissingNext _ 3 _ _ call5_kept_x19 call5_kept_x18 call5_after); [exact Hg|reflexivity|reflexivity|].
  repeat first [eapply phRegsRenameP; [eassumption|] | eapply phRegsRenameL; [eassumption|]
    | eapply phRegsStart; eassumption
    | eapply phRegsAdvance; [eassumption|reflexivity|first [left; reflexivity | right; assumption | right; eapply phNamedNonzero; eassumption | right; apply walkRemainingNonzero; assumption]|]
    | eapply phRegsNext; [eassumption..|reflexivity|reflexivity|first [assumption | eapply phNamedNonzero; eassumption | apply walkRemainingNonzero; assumption]|]].
Qed.

(* edge 0x0194 -> 0x00a8: field 4 consumes everything left, required field 5 is missing *)
Lemma parentHeaderEdgeError_0194_00a8 (args : ParentHeaderArgs) (returnAddress : Z) (call6_after : DecodeItemOutcome) (call6_kept_x18 : bv 64) (call6_kept_x19 : bv 64) (call5_after : DecodeItemOutcome) (call5_kept_x18 : bv 64) (call5_kept_x19 : bv 64) (call4_after : DecodeItemOutcome) (call4_kept_x18 : bv 64) (call4_kept_x19 : bv 64) (call3_after : DecodeItemOutcome) (call3_kept_x18 : bv 64) (call3_kept_x19 : bv 64) (call2_after : DecodeItemOutcome) (call2_kept_x18 : bv 64) (call2_kept_x19 : bv 64) (call_after : DecodeItemOutcome) :
  (bv_unsigned (parentHeaderReturnAddress args) = returnAddress /\ parentHeaderArgsWellFormed args) ->
  zesu_named_eq call2_kept_x18 (listWord64At8 call_after) ->
  zesu_named_eq call2_kept_x19 (listWord64At0 call_after) ->
  zesu_named_eq call3_kept_x18 (bv_sub call2_kept_x18 (listWord64At24 call2_after)) ->
  zesu_named_eq call3_kept_x19 (bv_add call2_kept_x19 (listWord64At24 call2_after)) ->
  zesu_named_eq call4_kept_x18 (bv_sub call3_kept_x18 (listWord64At24 call3_after)) ->
  zesu_named_eq call4_kept_x19 (bv_add call3_kept_x19 (listWord64At24 call3_after)) ->
  zesu_named_eq call5_kept_x18 (bv_sub call4_kept_x18 (listWord64At24 call4_after)) ->
  zesu_named_eq call5_kept_x19 (bv_add call4_kept_x19 (listWord64At24 call4_after)) ->
  zesu_named_eq call6_kept_x18 (bv_sub call5_kept_x18 (listWord64At24 call5_after)) ->
  zesu_named_eq call6_kept_x19 (bv_add call5_kept_x19 (listWord64At24 call5_after)) ->
  Pilot0194Entries.fp_machineAt0194_ForwardA0N0_Hist args returnAddress call6_after call6_kept_x18 call6_kept_x19 call5_after call5_kept_x18 call5_kept_x19 call4_after call4_kept_x18 call4_kept_x19 call3_after call3_kept_x18 call3_kept_x19 call2_after call2_kept_x18 call2_kept_x19 call_after ->
  call6_kept_x18 = listWord64At24 call6_after ->
  candidateParentHeader (parentHeaderInputBytes args) = candidateHeaderError.
Proof.
  intros [_ Hwf] ? ? ? ? ? ? ? ? ? ? Hh Hg.
  unfold Pilot0194Entries.fp_machineAt0194_ForwardA0N0_Hist in Hh. decompose [ex and] Hh.
  eapply (phMissingNext _ 4 _ _ call6_kept_x19 call6_kept_x18 call6_after); [exact Hg|reflexivity|reflexivity|].
  repeat first [eapply phRegsRenameP; [eassumption|] | eapply phRegsRenameL; [eassumption|]
    | eapply phRegsStart; eassumption
    | eapply phRegsAdvance; [eassumption|reflexivity|first [left; reflexivity | right; assumption | right; eapply phNamedNonzero; eassumption | right; apply walkRemainingNonzero; assumption]|]
    | eapply phRegsNext; [eassumption..|reflexivity|reflexivity|first [assumption | eapply phNamedNonzero; eassumption | apply walkRemainingNonzero; assumption]|]].
Qed.

(* edge 0x01c0 -> 0x00a8: field 5 consumes everything left, required field 6 is missing *)
Lemma parentHeaderEdgeError_01c0_00a8 (args : ParentHeaderArgs) (returnAddress : Z) (call7_after : DecodeItemOutcome) (call7_kept_x18 : bv 64) (call7_kept_x19 : bv 64) (call6_after : DecodeItemOutcome) (call6_kept_x18 : bv 64) (call6_kept_x19 : bv 64) (call5_after : DecodeItemOutcome) (call5_kept_x18 : bv 64) (call5_kept_x19 : bv 64) (call4_after : DecodeItemOutcome) (call4_kept_x18 : bv 64) (call4_kept_x19 : bv 64) (call3_after : DecodeItemOutcome) (call3_kept_x18 : bv 64) (call3_kept_x19 : bv 64) (call2_after : DecodeItemOutcome) (call2_kept_x18 : bv 64) (call2_kept_x19 : bv 64) (call_after : DecodeItemOutcome) :
  (bv_unsigned (parentHeaderReturnAddress args) = returnAddress /\ parentHeaderArgsWellFormed args) ->
  zesu_named_eq call2_kept_x18 (listWord64At8 call_after) ->
  zesu_named_eq call2_kept_x19 (listWord64At0 call_after) ->
  zesu_named_eq call3_kept_x18 (bv_sub call2_kept_x18 (listWord64At24 call2_after)) ->
  zesu_named_eq call3_kept_x19 (bv_add call2_kept_x19 (listWord64At24 call2_after)) ->
  zesu_named_eq call4_kept_x18 (bv_sub call3_kept_x18 (listWord64At24 call3_after)) ->
  zesu_named_eq call4_kept_x19 (bv_add call3_kept_x19 (listWord64At24 call3_after)) ->
  zesu_named_eq call5_kept_x18 (bv_sub call4_kept_x18 (listWord64At24 call4_after)) ->
  zesu_named_eq call5_kept_x19 (bv_add call4_kept_x19 (listWord64At24 call4_after)) ->
  zesu_named_eq call6_kept_x18 (bv_sub call5_kept_x18 (listWord64At24 call5_after)) ->
  zesu_named_eq call6_kept_x19 (bv_add call5_kept_x19 (listWord64At24 call5_after)) ->
  zesu_named_eq call7_kept_x18 (bv_sub call6_kept_x18 (listWord64At24 call6_after)) ->
  zesu_named_eq call7_kept_x19 (bv_add call6_kept_x19 (listWord64At24 call6_after)) ->
  Pilot01c0Entries.fp_machineAt01c0_ForwardA0N0_Hist args returnAddress call7_after call7_kept_x18 call7_kept_x19 call6_after call6_kept_x18 call6_kept_x19 call5_after call5_kept_x18 call5_kept_x19 call4_after call4_kept_x18 call4_kept_x19 call3_after call3_kept_x18 call3_kept_x19 call2_after call2_kept_x18 call2_kept_x19 call_after ->
  call7_kept_x18 = listWord64At24 call7_after ->
  candidateParentHeader (parentHeaderInputBytes args) = candidateHeaderError.
Proof.
  intros [_ Hwf] ? ? ? ? ? ? ? ? ? ? ? ? Hh Hg.
  unfold Pilot01c0Entries.fp_machineAt01c0_ForwardA0N0_Hist in Hh. decompose [ex and] Hh.
  eapply (phMissingNext _ 5 _ _ call7_kept_x19 call7_kept_x18 call7_after); [exact Hg|reflexivity|reflexivity|].
  repeat first [eapply phRegsRenameP; [eassumption|] | eapply phRegsRenameL; [eassumption|]
    | eapply phRegsStart; eassumption
    | eapply phRegsAdvance; [eassumption|reflexivity|first [left; reflexivity | right; assumption | right; eapply phNamedNonzero; eassumption | right; apply walkRemainingNonzero; assumption]|]
    | eapply phRegsNext; [eassumption..|reflexivity|reflexivity|first [assumption | eapply phNamedNonzero; eassumption | apply walkRemainingNonzero; assumption]|]].
Qed.

(* edge 0x01ec -> 0x00a8: field 6 consumes everything left, required field 7 is missing *)
Lemma parentHeaderEdgeError_01ec_00a8 (args : ParentHeaderArgs) (returnAddress : Z) (call8_after : DecodeItemOutcome) (call8_kept_x18 : bv 64) (call8_kept_x19 : bv 64) (call7_after : DecodeItemOutcome) (call7_kept_x18 : bv 64) (call7_kept_x19 : bv 64) (call6_after : DecodeItemOutcome) (call6_kept_x18 : bv 64) (call6_kept_x19 : bv 64) (call5_after : DecodeItemOutcome) (call5_kept_x18 : bv 64) (call5_kept_x19 : bv 64) (call4_after : DecodeItemOutcome) (call4_kept_x18 : bv 64) (call4_kept_x19 : bv 64) (call3_after : DecodeItemOutcome) (call3_kept_x18 : bv 64) (call3_kept_x19 : bv 64) (call2_after : DecodeItemOutcome) (call2_kept_x18 : bv 64) (call2_kept_x19 : bv 64) (call_after : DecodeItemOutcome) :
  (bv_unsigned (parentHeaderReturnAddress args) = returnAddress /\ parentHeaderArgsWellFormed args) ->
  zesu_named_eq call2_kept_x18 (listWord64At8 call_after) ->
  zesu_named_eq call2_kept_x19 (listWord64At0 call_after) ->
  zesu_named_eq call3_kept_x18 (bv_sub call2_kept_x18 (listWord64At24 call2_after)) ->
  zesu_named_eq call3_kept_x19 (bv_add call2_kept_x19 (listWord64At24 call2_after)) ->
  zesu_named_eq call4_kept_x18 (bv_sub call3_kept_x18 (listWord64At24 call3_after)) ->
  zesu_named_eq call4_kept_x19 (bv_add call3_kept_x19 (listWord64At24 call3_after)) ->
  zesu_named_eq call5_kept_x18 (bv_sub call4_kept_x18 (listWord64At24 call4_after)) ->
  zesu_named_eq call5_kept_x19 (bv_add call4_kept_x19 (listWord64At24 call4_after)) ->
  zesu_named_eq call6_kept_x18 (bv_sub call5_kept_x18 (listWord64At24 call5_after)) ->
  zesu_named_eq call6_kept_x19 (bv_add call5_kept_x19 (listWord64At24 call5_after)) ->
  zesu_named_eq call7_kept_x18 (bv_sub call6_kept_x18 (listWord64At24 call6_after)) ->
  zesu_named_eq call7_kept_x19 (bv_add call6_kept_x19 (listWord64At24 call6_after)) ->
  zesu_named_eq call8_kept_x18 (bv_sub call7_kept_x18 (listWord64At24 call7_after)) ->
  zesu_named_eq call8_kept_x19 (bv_add call7_kept_x19 (listWord64At24 call7_after)) ->
  Pilot01ecEntries.fp_machineAt01ec_ForwardA0N0_Hist args returnAddress call8_after call8_kept_x18 call8_kept_x19 call7_after call7_kept_x18 call7_kept_x19 call6_after call6_kept_x18 call6_kept_x19 call5_after call5_kept_x18 call5_kept_x19 call4_after call4_kept_x18 call4_kept_x19 call3_after call3_kept_x18 call3_kept_x19 call2_after call2_kept_x18 call2_kept_x19 call_after ->
  call8_kept_x18 = listWord64At24 call8_after ->
  candidateParentHeader (parentHeaderInputBytes args) = candidateHeaderError.
Proof.
  intros [_ Hwf] ? ? ? ? ? ? ? ? ? ? ? ? ? ? Hh Hg.
  unfold Pilot01ecEntries.fp_machineAt01ec_ForwardA0N0_Hist in Hh. decompose [ex and] Hh.
  eapply (phMissingNext _ 6 _ _ call8_kept_x19 call8_kept_x18 call8_after); [exact Hg|reflexivity|reflexivity|].
  repeat first [eapply phRegsRenameP; [eassumption|] | eapply phRegsRenameL; [eassumption|]
    | eapply phRegsStart; eassumption
    | eapply phRegsAdvance; [eassumption|reflexivity|first [left; reflexivity | right; assumption | right; eapply phNamedNonzero; eassumption | right; apply walkRemainingNonzero; assumption]|]
    | eapply phRegsNext; [eassumption..|reflexivity|reflexivity|first [assumption | eapply phNamedNonzero; eassumption | apply walkRemainingNonzero; assumption]|]].
Qed.

(* edge 0x0218 -> 0x00a8: field 7 consumes everything left, required field 8 is missing *)
Lemma parentHeaderEdgeError_0218_00a8 (args : ParentHeaderArgs) (returnAddress : Z) (call9_after : DecodeItemOutcome) (call9_kept_x18 : bv 64) (call9_kept_x19 : bv 64) (call8_after : DecodeItemOutcome) (call8_kept_x18 : bv 64) (call8_kept_x19 : bv 64) (call7_after : DecodeItemOutcome) (call7_kept_x18 : bv 64) (call7_kept_x19 : bv 64) (call6_after : DecodeItemOutcome) (call6_kept_x18 : bv 64) (call6_kept_x19 : bv 64) (call5_after : DecodeItemOutcome) (call5_kept_x18 : bv 64) (call5_kept_x19 : bv 64) (call4_after : DecodeItemOutcome) (call4_kept_x18 : bv 64) (call4_kept_x19 : bv 64) (call3_after : DecodeItemOutcome) (call3_kept_x18 : bv 64) (call3_kept_x19 : bv 64) (call2_after : DecodeItemOutcome) (call2_kept_x18 : bv 64) (call2_kept_x19 : bv 64) (call_after : DecodeItemOutcome) :
  (bv_unsigned (parentHeaderReturnAddress args) = returnAddress /\ parentHeaderArgsWellFormed args) ->
  zesu_named_eq call2_kept_x18 (listWord64At8 call_after) ->
  zesu_named_eq call2_kept_x19 (listWord64At0 call_after) ->
  zesu_named_eq call3_kept_x18 (bv_sub call2_kept_x18 (listWord64At24 call2_after)) ->
  zesu_named_eq call3_kept_x19 (bv_add call2_kept_x19 (listWord64At24 call2_after)) ->
  zesu_named_eq call4_kept_x18 (bv_sub call3_kept_x18 (listWord64At24 call3_after)) ->
  zesu_named_eq call4_kept_x19 (bv_add call3_kept_x19 (listWord64At24 call3_after)) ->
  zesu_named_eq call5_kept_x18 (bv_sub call4_kept_x18 (listWord64At24 call4_after)) ->
  zesu_named_eq call5_kept_x19 (bv_add call4_kept_x19 (listWord64At24 call4_after)) ->
  zesu_named_eq call6_kept_x18 (bv_sub call5_kept_x18 (listWord64At24 call5_after)) ->
  zesu_named_eq call6_kept_x19 (bv_add call5_kept_x19 (listWord64At24 call5_after)) ->
  zesu_named_eq call7_kept_x18 (bv_sub call6_kept_x18 (listWord64At24 call6_after)) ->
  zesu_named_eq call7_kept_x19 (bv_add call6_kept_x19 (listWord64At24 call6_after)) ->
  zesu_named_eq call8_kept_x18 (bv_sub call7_kept_x18 (listWord64At24 call7_after)) ->
  zesu_named_eq call8_kept_x19 (bv_add call7_kept_x19 (listWord64At24 call7_after)) ->
  zesu_named_eq call9_kept_x18 (bv_sub call8_kept_x18 (listWord64At24 call8_after)) ->
  zesu_named_eq call9_kept_x19 (bv_add call8_kept_x19 (listWord64At24 call8_after)) ->
  Pilot0218Entries.fp_machineAt0218_ForwardA0N0_Hist args returnAddress call9_after call9_kept_x18 call9_kept_x19 call8_after call8_kept_x18 call8_kept_x19 call7_after call7_kept_x18 call7_kept_x19 call6_after call6_kept_x18 call6_kept_x19 call5_after call5_kept_x18 call5_kept_x19 call4_after call4_kept_x18 call4_kept_x19 call3_after call3_kept_x18 call3_kept_x19 call2_after call2_kept_x18 call2_kept_x19 call_after ->
  call9_kept_x18 = listWord64At24 call9_after ->
  candidateParentHeader (parentHeaderInputBytes args) = candidateHeaderError.
Proof.
  intros [_ Hwf] ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? Hh Hg.
  unfold Pilot0218Entries.fp_machineAt0218_ForwardA0N0_Hist in Hh. decompose [ex and] Hh.
  eapply (phMissingNext _ 7 _ _ call9_kept_x19 call9_kept_x18 call9_after); [exact Hg|reflexivity|reflexivity|].
  repeat first [eapply phRegsRenameP; [eassumption|] | eapply phRegsRenameL; [eassumption|]
    | eapply phRegsStart; eassumption
    | eapply phRegsAdvance; [eassumption|reflexivity|first [left; reflexivity | right; assumption | right; eapply phNamedNonzero; eassumption | right; apply walkRemainingNonzero; assumption]|]
    | eapply phRegsNext; [eassumption..|reflexivity|reflexivity|first [assumption | eapply phNamedNonzero; eassumption | apply walkRemainingNonzero; assumption]|]].
Qed.
