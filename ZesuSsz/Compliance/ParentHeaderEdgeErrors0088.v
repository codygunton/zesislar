(* Step 2.4 M1, per-edge reason facts of the decodeItem-failure join 0x0088 (the call of field 0 to 8 fails).
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
Require ZesuSsz.Generated.DecodeParentHeader.FP301.Pilot0080Entries.
Require ZesuSsz.Generated.DecodeParentHeader.FP301.Pilot0108Entries.
Require ZesuSsz.Generated.DecodeParentHeader.FP301.Pilot0134Entries.
Require ZesuSsz.Generated.DecodeParentHeader.FP301.Pilot0160Entries.
Require ZesuSsz.Generated.DecodeParentHeader.FP301.Pilot018cEntries.
Require ZesuSsz.Generated.DecodeParentHeader.FP301.Pilot01b8Entries.
Require ZesuSsz.Generated.DecodeParentHeader.FP301.Pilot01e4Entries.
Require ZesuSsz.Generated.DecodeParentHeader.FP301.Pilot0210Entries.
Require ZesuSsz.Generated.DecodeParentHeader.FP301.Pilot023cEntries.

Import ListNotations.
Open Scope Z_scope.

(* edge 0x0080 -> 0x0088: field 0's decodeItem call fails *)
Lemma parentHeaderEdgeError_0080_0088 (args : ParentHeaderArgs) (returnAddress : Z) (call_after : DecodeItemOutcome) (call2_after : DecodeItemOutcome) (call2_kept_x18 : bv 64) (call2_kept_x19 : bv 64) :
  (bv_unsigned (parentHeaderReturnAddress args) = returnAddress /\ parentHeaderArgsWellFormed args) ->
  zesu_named_eq call2_kept_x18 (listWord64At8 call_after) ->
  zesu_named_eq call2_kept_x19 (listWord64At0 call_after) ->
  phCallMeaning args call2_kept_x19 call2_kept_x18 call2_after ->
  Pilot0080Entries.fp_machineAt0080_ForwardA0N0_Hist args returnAddress call_after ->
  bv_unsigned (bv_concat 16 (List.nth 33 call2_after (BV 8 0)) (List.nth 32 call2_after (BV 8 0))) <> 0 ->
  candidateParentHeader (parentHeaderInputBytes args) = candidateHeaderError.
Proof.
  intros [_ Hwf] ? ? (? & ? & ? & ? & ? & ?) Hh Hg.
  unfold Pilot0080Entries.fp_machineAt0080_ForwardA0N0_Hist in Hh. decompose [ex and] Hh.
  eapply (phFieldError _ 0 _ _ call2_kept_x19 call2_kept_x18); [exact Hg|eassumption|reflexivity|first [left; reflexivity | right; assumption | right; eapply phNamedNonzero; eassumption | right; apply walkRemainingNonzero; assumption]|].
  repeat first [eapply phRegsRenameP; [eassumption|] | eapply phRegsRenameL; [eassumption|]
    | eapply phRegsStart; eassumption
    | eapply phRegsAdvance; [eassumption|reflexivity|first [left; reflexivity | right; assumption | right; eapply phNamedNonzero; eassumption | right; apply walkRemainingNonzero; assumption]|]
    | eapply phRegsNext; [eassumption..|reflexivity|reflexivity|first [assumption | eapply phNamedNonzero; eassumption | apply walkRemainingNonzero; assumption]|]].
Qed.

(* edge 0x0108 -> 0x0088: field 1's decodeItem call fails *)
Lemma parentHeaderEdgeError_0108_0088 (args : ParentHeaderArgs) (returnAddress : Z) (call2_after : DecodeItemOutcome) (call2_kept_x18 : bv 64) (call2_kept_x19 : bv 64) (call_after : DecodeItemOutcome) (call3_after : DecodeItemOutcome) (call3_kept_x18 : bv 64) (call3_kept_x19 : bv 64) :
  (bv_unsigned (parentHeaderReturnAddress args) = returnAddress /\ parentHeaderArgsWellFormed args) ->
  zesu_named_eq call2_kept_x18 (listWord64At8 call_after) ->
  zesu_named_eq call2_kept_x19 (listWord64At0 call_after) ->
  zesu_named_eq call3_kept_x18 (bv_sub call2_kept_x18 (listWord64At24 call2_after)) ->
  zesu_named_eq call3_kept_x19 (bv_add call2_kept_x19 (listWord64At24 call2_after)) ->
  phCallMeaning args call3_kept_x19 call3_kept_x18 call3_after ->
  Pilot0108Entries.fp_machineAt0108_ForwardA0N0_Hist args returnAddress call2_after call2_kept_x18 call2_kept_x19 call_after ->
  bv_unsigned (bv_concat 16 (List.nth 33 call3_after (BV 8 0)) (List.nth 32 call3_after (BV 8 0))) <> 0 ->
  candidateParentHeader (parentHeaderInputBytes args) = candidateHeaderError.
Proof.
  intros [_ Hwf] ? ? ? ? (? & ? & ? & ? & ? & ?) Hh Hg.
  unfold Pilot0108Entries.fp_machineAt0108_ForwardA0N0_Hist in Hh. decompose [ex and] Hh.
  eapply (phFieldError _ 1 _ _ call3_kept_x19 call3_kept_x18); [exact Hg|eassumption|reflexivity|first [left; reflexivity | right; assumption | right; eapply phNamedNonzero; eassumption | right; apply walkRemainingNonzero; assumption]|].
  repeat first [eapply phRegsRenameP; [eassumption|] | eapply phRegsRenameL; [eassumption|]
    | eapply phRegsStart; eassumption
    | eapply phRegsAdvance; [eassumption|reflexivity|first [left; reflexivity | right; assumption | right; eapply phNamedNonzero; eassumption | right; apply walkRemainingNonzero; assumption]|]
    | eapply phRegsNext; [eassumption..|reflexivity|reflexivity|first [assumption | eapply phNamedNonzero; eassumption | apply walkRemainingNonzero; assumption]|]].
Qed.

(* edge 0x0134 -> 0x0088: field 2's decodeItem call fails *)
Lemma parentHeaderEdgeError_0134_0088 (args : ParentHeaderArgs) (returnAddress : Z) (call3_after : DecodeItemOutcome) (call3_kept_x18 : bv 64) (call3_kept_x19 : bv 64) (call2_after : DecodeItemOutcome) (call2_kept_x18 : bv 64) (call2_kept_x19 : bv 64) (call_after : DecodeItemOutcome) (call4_after : DecodeItemOutcome) (call4_kept_x18 : bv 64) (call4_kept_x19 : bv 64) :
  (bv_unsigned (parentHeaderReturnAddress args) = returnAddress /\ parentHeaderArgsWellFormed args) ->
  zesu_named_eq call2_kept_x18 (listWord64At8 call_after) ->
  zesu_named_eq call2_kept_x19 (listWord64At0 call_after) ->
  zesu_named_eq call3_kept_x18 (bv_sub call2_kept_x18 (listWord64At24 call2_after)) ->
  zesu_named_eq call3_kept_x19 (bv_add call2_kept_x19 (listWord64At24 call2_after)) ->
  zesu_named_eq call4_kept_x18 (bv_sub call3_kept_x18 (listWord64At24 call3_after)) ->
  zesu_named_eq call4_kept_x19 (bv_add call3_kept_x19 (listWord64At24 call3_after)) ->
  phCallMeaning args call4_kept_x19 call4_kept_x18 call4_after ->
  Pilot0134Entries.fp_machineAt0134_ForwardA0N0_Hist args returnAddress call3_after call3_kept_x18 call3_kept_x19 call2_after call2_kept_x18 call2_kept_x19 call_after ->
  bv_unsigned (bv_concat 16 (List.nth 33 call4_after (BV 8 0)) (List.nth 32 call4_after (BV 8 0))) <> 0 ->
  candidateParentHeader (parentHeaderInputBytes args) = candidateHeaderError.
Proof.
  intros [_ Hwf] ? ? ? ? ? ? (? & ? & ? & ? & ? & ?) Hh Hg.
  unfold Pilot0134Entries.fp_machineAt0134_ForwardA0N0_Hist in Hh. decompose [ex and] Hh.
  eapply (phFieldError _ 2 _ _ call4_kept_x19 call4_kept_x18); [exact Hg|eassumption|reflexivity|first [left; reflexivity | right; assumption | right; eapply phNamedNonzero; eassumption | right; apply walkRemainingNonzero; assumption]|].
  repeat first [eapply phRegsRenameP; [eassumption|] | eapply phRegsRenameL; [eassumption|]
    | eapply phRegsStart; eassumption
    | eapply phRegsAdvance; [eassumption|reflexivity|first [left; reflexivity | right; assumption | right; eapply phNamedNonzero; eassumption | right; apply walkRemainingNonzero; assumption]|]
    | eapply phRegsNext; [eassumption..|reflexivity|reflexivity|first [assumption | eapply phNamedNonzero; eassumption | apply walkRemainingNonzero; assumption]|]].
Qed.

(* edge 0x0160 -> 0x0088: field 3's decodeItem call fails *)
Lemma parentHeaderEdgeError_0160_0088 (args : ParentHeaderArgs) (returnAddress : Z) (call4_after : DecodeItemOutcome) (call4_kept_x18 : bv 64) (call4_kept_x19 : bv 64) (call3_after : DecodeItemOutcome) (call3_kept_x18 : bv 64) (call3_kept_x19 : bv 64) (call2_after : DecodeItemOutcome) (call2_kept_x18 : bv 64) (call2_kept_x19 : bv 64) (call_after : DecodeItemOutcome) (call5_after : DecodeItemOutcome) (call5_kept_x18 : bv 64) (call5_kept_x19 : bv 64) :
  (bv_unsigned (parentHeaderReturnAddress args) = returnAddress /\ parentHeaderArgsWellFormed args) ->
  zesu_named_eq call2_kept_x18 (listWord64At8 call_after) ->
  zesu_named_eq call2_kept_x19 (listWord64At0 call_after) ->
  zesu_named_eq call3_kept_x18 (bv_sub call2_kept_x18 (listWord64At24 call2_after)) ->
  zesu_named_eq call3_kept_x19 (bv_add call2_kept_x19 (listWord64At24 call2_after)) ->
  zesu_named_eq call4_kept_x18 (bv_sub call3_kept_x18 (listWord64At24 call3_after)) ->
  zesu_named_eq call4_kept_x19 (bv_add call3_kept_x19 (listWord64At24 call3_after)) ->
  zesu_named_eq call5_kept_x18 (bv_sub call4_kept_x18 (listWord64At24 call4_after)) ->
  zesu_named_eq call5_kept_x19 (bv_add call4_kept_x19 (listWord64At24 call4_after)) ->
  phCallMeaning args call5_kept_x19 call5_kept_x18 call5_after ->
  Pilot0160Entries.fp_machineAt0160_ForwardA0N0_Hist args returnAddress call4_after call4_kept_x18 call4_kept_x19 call3_after call3_kept_x18 call3_kept_x19 call2_after call2_kept_x18 call2_kept_x19 call_after ->
  bv_unsigned (bv_concat 16 (List.nth 33 call5_after (BV 8 0)) (List.nth 32 call5_after (BV 8 0))) <> 0 ->
  candidateParentHeader (parentHeaderInputBytes args) = candidateHeaderError.
Proof.
  intros [_ Hwf] ? ? ? ? ? ? ? ? (? & ? & ? & ? & ? & ?) Hh Hg.
  unfold Pilot0160Entries.fp_machineAt0160_ForwardA0N0_Hist in Hh. decompose [ex and] Hh.
  eapply (phFieldError _ 3 _ _ call5_kept_x19 call5_kept_x18); [exact Hg|eassumption|reflexivity|first [left; reflexivity | right; assumption | right; eapply phNamedNonzero; eassumption | right; apply walkRemainingNonzero; assumption]|].
  repeat first [eapply phRegsRenameP; [eassumption|] | eapply phRegsRenameL; [eassumption|]
    | eapply phRegsStart; eassumption
    | eapply phRegsAdvance; [eassumption|reflexivity|first [left; reflexivity | right; assumption | right; eapply phNamedNonzero; eassumption | right; apply walkRemainingNonzero; assumption]|]
    | eapply phRegsNext; [eassumption..|reflexivity|reflexivity|first [assumption | eapply phNamedNonzero; eassumption | apply walkRemainingNonzero; assumption]|]].
Qed.

(* edge 0x018c -> 0x0088: field 4's decodeItem call fails *)
Lemma parentHeaderEdgeError_018c_0088 (args : ParentHeaderArgs) (returnAddress : Z) (call5_after : DecodeItemOutcome) (call5_kept_x18 : bv 64) (call5_kept_x19 : bv 64) (call4_after : DecodeItemOutcome) (call4_kept_x18 : bv 64) (call4_kept_x19 : bv 64) (call3_after : DecodeItemOutcome) (call3_kept_x18 : bv 64) (call3_kept_x19 : bv 64) (call2_after : DecodeItemOutcome) (call2_kept_x18 : bv 64) (call2_kept_x19 : bv 64) (call_after : DecodeItemOutcome) (call6_after : DecodeItemOutcome) (call6_kept_x18 : bv 64) (call6_kept_x19 : bv 64) :
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
  phCallMeaning args call6_kept_x19 call6_kept_x18 call6_after ->
  Pilot018cEntries.fp_machineAt018c_ForwardA0N0_Hist args returnAddress call5_after call5_kept_x18 call5_kept_x19 call4_after call4_kept_x18 call4_kept_x19 call3_after call3_kept_x18 call3_kept_x19 call2_after call2_kept_x18 call2_kept_x19 call_after ->
  bv_unsigned (bv_concat 16 (List.nth 33 call6_after (BV 8 0)) (List.nth 32 call6_after (BV 8 0))) <> 0 ->
  candidateParentHeader (parentHeaderInputBytes args) = candidateHeaderError.
Proof.
  intros [_ Hwf] ? ? ? ? ? ? ? ? ? ? (? & ? & ? & ? & ? & ?) Hh Hg.
  unfold Pilot018cEntries.fp_machineAt018c_ForwardA0N0_Hist in Hh. decompose [ex and] Hh.
  eapply (phFieldError _ 4 _ _ call6_kept_x19 call6_kept_x18); [exact Hg|eassumption|reflexivity|first [left; reflexivity | right; assumption | right; eapply phNamedNonzero; eassumption | right; apply walkRemainingNonzero; assumption]|].
  repeat first [eapply phRegsRenameP; [eassumption|] | eapply phRegsRenameL; [eassumption|]
    | eapply phRegsStart; eassumption
    | eapply phRegsAdvance; [eassumption|reflexivity|first [left; reflexivity | right; assumption | right; eapply phNamedNonzero; eassumption | right; apply walkRemainingNonzero; assumption]|]
    | eapply phRegsNext; [eassumption..|reflexivity|reflexivity|first [assumption | eapply phNamedNonzero; eassumption | apply walkRemainingNonzero; assumption]|]].
Qed.

(* edge 0x01b8 -> 0x0088: field 5's decodeItem call fails *)
Lemma parentHeaderEdgeError_01b8_0088 (args : ParentHeaderArgs) (returnAddress : Z) (call6_after : DecodeItemOutcome) (call6_kept_x18 : bv 64) (call6_kept_x19 : bv 64) (call5_after : DecodeItemOutcome) (call5_kept_x18 : bv 64) (call5_kept_x19 : bv 64) (call4_after : DecodeItemOutcome) (call4_kept_x18 : bv 64) (call4_kept_x19 : bv 64) (call3_after : DecodeItemOutcome) (call3_kept_x18 : bv 64) (call3_kept_x19 : bv 64) (call2_after : DecodeItemOutcome) (call2_kept_x18 : bv 64) (call2_kept_x19 : bv 64) (call_after : DecodeItemOutcome) (call7_after : DecodeItemOutcome) (call7_kept_x18 : bv 64) (call7_kept_x19 : bv 64) :
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
  phCallMeaning args call7_kept_x19 call7_kept_x18 call7_after ->
  Pilot01b8Entries.fp_machineAt01b8_ForwardA0N0_Hist args returnAddress call6_after call6_kept_x18 call6_kept_x19 call5_after call5_kept_x18 call5_kept_x19 call4_after call4_kept_x18 call4_kept_x19 call3_after call3_kept_x18 call3_kept_x19 call2_after call2_kept_x18 call2_kept_x19 call_after ->
  bv_unsigned (bv_concat 16 (List.nth 33 call7_after (BV 8 0)) (List.nth 32 call7_after (BV 8 0))) <> 0 ->
  candidateParentHeader (parentHeaderInputBytes args) = candidateHeaderError.
Proof.
  intros [_ Hwf] ? ? ? ? ? ? ? ? ? ? ? ? (? & ? & ? & ? & ? & ?) Hh Hg.
  unfold Pilot01b8Entries.fp_machineAt01b8_ForwardA0N0_Hist in Hh. decompose [ex and] Hh.
  eapply (phFieldError _ 5 _ _ call7_kept_x19 call7_kept_x18); [exact Hg|eassumption|reflexivity|first [left; reflexivity | right; assumption | right; eapply phNamedNonzero; eassumption | right; apply walkRemainingNonzero; assumption]|].
  repeat first [eapply phRegsRenameP; [eassumption|] | eapply phRegsRenameL; [eassumption|]
    | eapply phRegsStart; eassumption
    | eapply phRegsAdvance; [eassumption|reflexivity|first [left; reflexivity | right; assumption | right; eapply phNamedNonzero; eassumption | right; apply walkRemainingNonzero; assumption]|]
    | eapply phRegsNext; [eassumption..|reflexivity|reflexivity|first [assumption | eapply phNamedNonzero; eassumption | apply walkRemainingNonzero; assumption]|]].
Qed.

(* edge 0x01e4 -> 0x0088: field 6's decodeItem call fails *)
Lemma parentHeaderEdgeError_01e4_0088 (args : ParentHeaderArgs) (returnAddress : Z) (call7_after : DecodeItemOutcome) (call7_kept_x18 : bv 64) (call7_kept_x19 : bv 64) (call6_after : DecodeItemOutcome) (call6_kept_x18 : bv 64) (call6_kept_x19 : bv 64) (call5_after : DecodeItemOutcome) (call5_kept_x18 : bv 64) (call5_kept_x19 : bv 64) (call4_after : DecodeItemOutcome) (call4_kept_x18 : bv 64) (call4_kept_x19 : bv 64) (call3_after : DecodeItemOutcome) (call3_kept_x18 : bv 64) (call3_kept_x19 : bv 64) (call2_after : DecodeItemOutcome) (call2_kept_x18 : bv 64) (call2_kept_x19 : bv 64) (call_after : DecodeItemOutcome) (call8_after : DecodeItemOutcome) (call8_kept_x18 : bv 64) (call8_kept_x19 : bv 64) :
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
  phCallMeaning args call8_kept_x19 call8_kept_x18 call8_after ->
  Pilot01e4Entries.fp_machineAt01e4_ForwardA0N0_Hist args returnAddress call7_after call7_kept_x18 call7_kept_x19 call6_after call6_kept_x18 call6_kept_x19 call5_after call5_kept_x18 call5_kept_x19 call4_after call4_kept_x18 call4_kept_x19 call3_after call3_kept_x18 call3_kept_x19 call2_after call2_kept_x18 call2_kept_x19 call_after ->
  bv_unsigned (bv_concat 16 (List.nth 33 call8_after (BV 8 0)) (List.nth 32 call8_after (BV 8 0))) <> 0 ->
  candidateParentHeader (parentHeaderInputBytes args) = candidateHeaderError.
Proof.
  intros [_ Hwf] ? ? ? ? ? ? ? ? ? ? ? ? ? ? (? & ? & ? & ? & ? & ?) Hh Hg.
  unfold Pilot01e4Entries.fp_machineAt01e4_ForwardA0N0_Hist in Hh. decompose [ex and] Hh.
  eapply (phFieldError _ 6 _ _ call8_kept_x19 call8_kept_x18); [exact Hg|eassumption|reflexivity|first [left; reflexivity | right; assumption | right; eapply phNamedNonzero; eassumption | right; apply walkRemainingNonzero; assumption]|].
  repeat first [eapply phRegsRenameP; [eassumption|] | eapply phRegsRenameL; [eassumption|]
    | eapply phRegsStart; eassumption
    | eapply phRegsAdvance; [eassumption|reflexivity|first [left; reflexivity | right; assumption | right; eapply phNamedNonzero; eassumption | right; apply walkRemainingNonzero; assumption]|]
    | eapply phRegsNext; [eassumption..|reflexivity|reflexivity|first [assumption | eapply phNamedNonzero; eassumption | apply walkRemainingNonzero; assumption]|]].
Qed.

(* edge 0x0210 -> 0x0088: field 7's decodeItem call fails *)
Lemma parentHeaderEdgeError_0210_0088 (args : ParentHeaderArgs) (returnAddress : Z) (call8_after : DecodeItemOutcome) (call8_kept_x18 : bv 64) (call8_kept_x19 : bv 64) (call7_after : DecodeItemOutcome) (call7_kept_x18 : bv 64) (call7_kept_x19 : bv 64) (call6_after : DecodeItemOutcome) (call6_kept_x18 : bv 64) (call6_kept_x19 : bv 64) (call5_after : DecodeItemOutcome) (call5_kept_x18 : bv 64) (call5_kept_x19 : bv 64) (call4_after : DecodeItemOutcome) (call4_kept_x18 : bv 64) (call4_kept_x19 : bv 64) (call3_after : DecodeItemOutcome) (call3_kept_x18 : bv 64) (call3_kept_x19 : bv 64) (call2_after : DecodeItemOutcome) (call2_kept_x18 : bv 64) (call2_kept_x19 : bv 64) (call_after : DecodeItemOutcome) (call9_after : DecodeItemOutcome) (call9_kept_x18 : bv 64) (call9_kept_x19 : bv 64) :
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
  phCallMeaning args call9_kept_x19 call9_kept_x18 call9_after ->
  Pilot0210Entries.fp_machineAt0210_ForwardA0N0_Hist args returnAddress call8_after call8_kept_x18 call8_kept_x19 call7_after call7_kept_x18 call7_kept_x19 call6_after call6_kept_x18 call6_kept_x19 call5_after call5_kept_x18 call5_kept_x19 call4_after call4_kept_x18 call4_kept_x19 call3_after call3_kept_x18 call3_kept_x19 call2_after call2_kept_x18 call2_kept_x19 call_after ->
  bv_unsigned (bv_concat 16 (List.nth 33 call9_after (BV 8 0)) (List.nth 32 call9_after (BV 8 0))) <> 0 ->
  candidateParentHeader (parentHeaderInputBytes args) = candidateHeaderError.
Proof.
  intros [_ Hwf] ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? (? & ? & ? & ? & ? & ?) Hh Hg.
  unfold Pilot0210Entries.fp_machineAt0210_ForwardA0N0_Hist in Hh. decompose [ex and] Hh.
  eapply (phFieldError _ 7 _ _ call9_kept_x19 call9_kept_x18); [exact Hg|eassumption|reflexivity|first [left; reflexivity | right; assumption | right; eapply phNamedNonzero; eassumption | right; apply walkRemainingNonzero; assumption]|].
  repeat first [eapply phRegsRenameP; [eassumption|] | eapply phRegsRenameL; [eassumption|]
    | eapply phRegsStart; eassumption
    | eapply phRegsAdvance; [eassumption|reflexivity|first [left; reflexivity | right; assumption | right; eapply phNamedNonzero; eassumption | right; apply walkRemainingNonzero; assumption]|]
    | eapply phRegsNext; [eassumption..|reflexivity|reflexivity|first [assumption | eapply phNamedNonzero; eassumption | apply walkRemainingNonzero; assumption]|]].
Qed.

(* edge 0x023c -> 0x0088: field 8's decodeItem call fails *)
Lemma parentHeaderEdgeError_023c_0088 (args : ParentHeaderArgs) (returnAddress : Z) (call9_after : DecodeItemOutcome) (call9_kept_x18 : bv 64) (call9_kept_x19 : bv 64) (call8_after : DecodeItemOutcome) (call8_kept_x18 : bv 64) (call8_kept_x19 : bv 64) (call7_after : DecodeItemOutcome) (call7_kept_x18 : bv 64) (call7_kept_x19 : bv 64) (call6_after : DecodeItemOutcome) (call6_kept_x18 : bv 64) (call6_kept_x19 : bv 64) (call5_after : DecodeItemOutcome) (call5_kept_x18 : bv 64) (call5_kept_x19 : bv 64) (call4_after : DecodeItemOutcome) (call4_kept_x18 : bv 64) (call4_kept_x19 : bv 64) (call3_after : DecodeItemOutcome) (call3_kept_x18 : bv 64) (call3_kept_x19 : bv 64) (call2_after : DecodeItemOutcome) (call2_kept_x18 : bv 64) (call2_kept_x19 : bv 64) (call_after : DecodeItemOutcome) (call10_after : DecodeItemOutcome) (call10_kept_x19 : bv 64) (call10_kept_x20 : bv 64) :
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
  zesu_named_eq call10_kept_x19 (bv_add call9_kept_x19 (listWord64At24 call9_after)) ->
  zesu_named_eq call10_kept_x20 (bv_sub call9_kept_x18 (listWord64At24 call9_after)) ->
  phCallMeaning args call10_kept_x19 call10_kept_x20 call10_after ->
  Pilot023cEntries.fp_machineAt023c_ForwardA0N0_Hist args returnAddress call9_after call9_kept_x18 call9_kept_x19 call8_after call8_kept_x18 call8_kept_x19 call7_after call7_kept_x18 call7_kept_x19 call6_after call6_kept_x18 call6_kept_x19 call5_after call5_kept_x18 call5_kept_x19 call4_after call4_kept_x18 call4_kept_x19 call3_after call3_kept_x18 call3_kept_x19 call2_after call2_kept_x18 call2_kept_x19 call_after ->
  bv_unsigned (bv_concat 16 (List.nth 33 call10_after (BV 8 0)) (List.nth 32 call10_after (BV 8 0))) <> 0 ->
  candidateParentHeader (parentHeaderInputBytes args) = candidateHeaderError.
Proof.
  intros [_ Hwf] ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? (? & ? & ? & ? & ? & ?) Hh Hg.
  unfold Pilot023cEntries.fp_machineAt023c_ForwardA0N0_Hist in Hh. decompose [ex and] Hh.
  eapply (phFieldError _ 8 _ _ call10_kept_x19 call10_kept_x20); [exact Hg|eassumption|reflexivity|first [left; reflexivity | right; assumption | right; eapply phNamedNonzero; eassumption | right; apply walkRemainingNonzero; assumption]|].
  repeat first [eapply phRegsRenameP; [eassumption|] | eapply phRegsRenameL; [eassumption|]
    | eapply phRegsStart; eassumption
    | eapply phRegsAdvance; [eassumption|reflexivity|first [left; reflexivity | right; assumption | right; eapply phNamedNonzero; eassumption | right; apply walkRemainingNonzero; assumption]|]
    | eapply phRegsNext; [eassumption..|reflexivity|reflexivity|first [assumption | eapply phNamedNonzero; eassumption | apply walkRemainingNonzero; assumption]|]].
Qed.
