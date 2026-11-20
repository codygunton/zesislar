(* Step 2.4 M1, per-edge reason facts of the integer-field join 0x026c (fields 9 to 11: the call fails, the item is a list, or its payload is longer than 8 bytes).
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
Require ZesuSsz.Generated.DecodeParentHeader.FP301.Pilot0264Entries.
Require ZesuSsz.Generated.DecodeParentHeader.FP301.Pilot02a4Entries.
Require ZesuSsz.Generated.DecodeParentHeader.FP301.Pilot02b0Entries.
Require ZesuSsz.Generated.DecodeParentHeader.FP301.Pilot0300Entries.
Require ZesuSsz.Generated.DecodeParentHeader.FP301.Pilot0308Entries.
Require ZesuSsz.Generated.DecodeParentHeader.FP301.Pilot0314Entries.
Require ZesuSsz.Generated.DecodeParentHeader.FP301.Pilot0368Entries.
Require ZesuSsz.Generated.DecodeParentHeader.FP301.Pilot0370Entries.
Require ZesuSsz.Generated.DecodeParentHeader.FP301.Pilot037cEntries.

Import ListNotations.
Open Scope Z_scope.

(* edge 0x0264 -> 0x026c: field 9's decodeItem call fails *)
Lemma parentHeaderEdgeError_0264_026c (args : ParentHeaderArgs) (returnAddress : Z) (call10_after : DecodeItemOutcome) (call10_kept_x19 : bv 64) (call10_kept_x20 : bv 64) (call9_after : DecodeItemOutcome) (call9_kept_x18 : bv 64) (call9_kept_x19 : bv 64) (call8_after : DecodeItemOutcome) (call8_kept_x18 : bv 64) (call8_kept_x19 : bv 64) (call7_after : DecodeItemOutcome) (call7_kept_x18 : bv 64) (call7_kept_x19 : bv 64) (call6_after : DecodeItemOutcome) (call6_kept_x18 : bv 64) (call6_kept_x19 : bv 64) (call5_after : DecodeItemOutcome) (call5_kept_x18 : bv 64) (call5_kept_x19 : bv 64) (call4_after : DecodeItemOutcome) (call4_kept_x18 : bv 64) (call4_kept_x19 : bv 64) (call3_after : DecodeItemOutcome) (call3_kept_x18 : bv 64) (call3_kept_x19 : bv 64) (call2_after : DecodeItemOutcome) (call2_kept_x18 : bv 64) (call2_kept_x19 : bv 64) (call_after : DecodeItemOutcome) (call11_after : DecodeItemOutcome) (call11_kept_x18 : bv 64) (call11_kept_x19 : bv 64) :
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
  zesu_named_eq call11_kept_x18 (bv_add call10_kept_x19 (listWord64At24 call10_after)) ->
  zesu_named_eq call11_kept_x19 (bv_sub call10_kept_x20 (listWord64At24 call10_after)) ->
  phCallMeaning args call11_kept_x18 call11_kept_x19 call11_after ->
  Pilot0264Entries.fp_machineAt0264_ForwardA0N0_Hist args returnAddress call10_after call10_kept_x19 call10_kept_x20 call9_after call9_kept_x18 call9_kept_x19 call8_after call8_kept_x18 call8_kept_x19 call7_after call7_kept_x18 call7_kept_x19 call6_after call6_kept_x18 call6_kept_x19 call5_after call5_kept_x18 call5_kept_x19 call4_after call4_kept_x18 call4_kept_x19 call3_after call3_kept_x18 call3_kept_x19 call2_after call2_kept_x18 call2_kept_x19 call_after ->
  bv_unsigned (bv_concat 16 (List.nth 33 call11_after (BV 8 0)) (List.nth 32 call11_after (BV 8 0))) <> 0 ->
  candidateParentHeader (parentHeaderInputBytes args) = candidateHeaderError.
Proof.
  intros [_ Hwf] ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? (? & ? & ? & ? & ? & ?) Hh Hg.
  unfold Pilot0264Entries.fp_machineAt0264_ForwardA0N0_Hist in Hh. decompose [ex and] Hh.
  eapply (phFieldError _ 9 _ _ call11_kept_x18 call11_kept_x19); [exact Hg|eassumption|reflexivity|first [left; reflexivity | right; assumption | right; eapply phNamedNonzero; eassumption | right; apply walkRemainingNonzero; assumption]|].
  repeat first [eapply phRegsRenameP; [eassumption|] | eapply phRegsRenameL; [eassumption|]
    | eapply phRegsStart; eassumption
    | eapply phRegsAdvance; [eassumption|reflexivity|first [left; reflexivity | right; assumption | right; eapply phNamedNonzero; eassumption | right; apply walkRemainingNonzero; assumption]|]
    | eapply phRegsNext; [eassumption..|reflexivity|reflexivity|first [assumption | eapply phNamedNonzero; eassumption | apply walkRemainingNonzero; assumption]|]].
Qed.

(* edge 0x02a4 -> 0x026c: integer field 9 is a list *)
Lemma parentHeaderEdgeError_02a4_026c (args : ParentHeaderArgs) (returnAddress : Z) (call11_after : DecodeItemOutcome) (call11_kept_x18 : bv 64) (call11_kept_x19 : bv 64) (call10_after : DecodeItemOutcome) (call10_kept_x20 : bv 64) (call_after : DecodeItemOutcome) :
  (bv_unsigned (parentHeaderReturnAddress args) = returnAddress /\ parentHeaderArgsWellFormed args) ->
  Pilot02a4Entries.fp_machineAt02a4_ForwardA0N0_Hist args returnAddress call11_after call11_kept_x18 call11_kept_x19 call10_after call10_kept_x20 call_after ->
  bv_unsigned (bv_and (bv_zero_extend 64 (List.nth 16 call11_after (BV 8 0))) (BV 64 1)) <> 0 ->
  candidateParentHeader (parentHeaderInputBytes args) = candidateHeaderError.
Proof.
  intros [_ Hwf] Hh Hg.
  unfold Pilot02a4Entries.fp_machineAt02a4_ForwardA0N0_Hist in Hh. decompose [ex and] Hh.
  eapply (phIntegerReject _ 9 _ _ call11_kept_x18 call11_kept_x19); [left; exact Hg|eassumption|eassumption|reflexivity..|].
  repeat first [eapply phRegsRenameP; [eassumption|] | eapply phRegsRenameL; [eassumption|]
    | eapply phRegsStart; eassumption
    | eapply phRegsAdvance; [eassumption|reflexivity|first [left; reflexivity | right; assumption | right; eapply phNamedNonzero; eassumption | right; apply walkRemainingNonzero; assumption]|]
    | eapply phRegsNext; [eassumption..|reflexivity|reflexivity|first [assumption | eapply phNamedNonzero; eassumption | apply walkRemainingNonzero; assumption]|]].
Qed.

(* edge 0x02b0 -> 0x026c: integer field 9 is longer than 8 bytes *)
Lemma parentHeaderEdgeError_02b0_026c (args : ParentHeaderArgs) (returnAddress : Z) (call11_after : DecodeItemOutcome) (call11_kept_x18 : bv 64) (call11_kept_x19 : bv 64) (call10_after : DecodeItemOutcome) (call10_kept_x20 : bv 64) (call_after : DecodeItemOutcome) :
  (bv_unsigned (parentHeaderReturnAddress args) = returnAddress /\ parentHeaderArgsWellFormed args) ->
  Pilot02b0Entries.fp_machineAt02b0_ForwardA0N0_Hist args returnAddress call11_after call11_kept_x18 call11_kept_x19 call10_after call10_kept_x20 call_after ->
  8 < bv_unsigned (listWord64At8 call11_after) ->
  candidateParentHeader (parentHeaderInputBytes args) = candidateHeaderError.
Proof.
  intros [_ Hwf] Hh Hg.
  unfold Pilot02b0Entries.fp_machineAt02b0_ForwardA0N0_Hist in Hh. decompose [ex and] Hh.
  eapply (phIntegerReject _ 9 _ _ call11_kept_x18 call11_kept_x19); [right; exact Hg|eassumption|eassumption|reflexivity..|].
  repeat first [eapply phRegsRenameP; [eassumption|] | eapply phRegsRenameL; [eassumption|]
    | eapply phRegsStart; eassumption
    | eapply phRegsAdvance; [eassumption|reflexivity|first [left; reflexivity | right; assumption | right; eapply phNamedNonzero; eassumption | right; apply walkRemainingNonzero; assumption]|]
    | eapply phRegsNext; [eassumption..|reflexivity|reflexivity|first [assumption | eapply phNamedNonzero; eassumption | apply walkRemainingNonzero; assumption]|]].
Qed.

(* edge 0x0300 -> 0x026c: field 10's decodeItem call fails *)
Lemma parentHeaderEdgeError_0300_026c (args : ParentHeaderArgs) (returnAddress : Z) (call11_after : DecodeItemOutcome) (call11_kept_x18 : bv 64) (call11_kept_x19 : bv 64) (call10_after : DecodeItemOutcome) (call10_kept_x20 : bv 64) (call_after : DecodeItemOutcome) (call12_after : DecodeItemOutcome) (call12_kept_x18 : bv 64) (call12_kept_x20 : bv 64) :
  (bv_unsigned (parentHeaderReturnAddress args) = returnAddress /\ parentHeaderArgsWellFormed args) ->
  zesu_named_eq call11_kept_x19 (bv_sub call10_kept_x20 (listWord64At24 call10_after)) ->
  zesu_named_eq call12_kept_x18 (bv_add call11_kept_x18 (listWord64At24 call11_after)) ->
  zesu_named_eq call12_kept_x20 (bv_sub call11_kept_x19 (listWord64At24 call11_after)) ->
  phCallMeaning args call12_kept_x18 call12_kept_x20 call12_after ->
  Pilot0300Entries.fp_machineAt0300_ForwardA0N0_Hist args returnAddress call11_after call11_kept_x18 call11_kept_x19 call10_after call10_kept_x20 call_after ->
  bv_unsigned (bv_concat 16 (List.nth 33 call12_after (BV 8 0)) (List.nth 32 call12_after (BV 8 0))) <> 0 ->
  candidateParentHeader (parentHeaderInputBytes args) = candidateHeaderError.
Proof.
  intros [_ Hwf] ? ? ? (? & ? & ? & ? & ? & ?) Hh Hg.
  unfold Pilot0300Entries.fp_machineAt0300_ForwardA0N0_Hist, ZesuSsz.Automation2.Hist.zesu_join_history in Hh. decompose [ex and] Hh.
  eapply (phFieldError _ 10 _ _ call12_kept_x18 call12_kept_x20); [exact Hg|eassumption|reflexivity|first [left; reflexivity | right; assumption | right; eapply phNamedNonzero; eassumption | right; apply walkRemainingNonzero; assumption]|].
  repeat first [eapply phRegsRenameP; [eassumption|] | eapply phRegsRenameL; [eassumption|]
    | eapply phRegsStart; eassumption
    | eapply phRegsAdvance; [eassumption|reflexivity|first [left; reflexivity | right; assumption | right; eapply phNamedNonzero; eassumption | right; apply walkRemainingNonzero; assumption]|]
    | eapply phRegsNext; [eassumption..|reflexivity|reflexivity|first [assumption | eapply phNamedNonzero; eassumption | apply walkRemainingNonzero; assumption]|]].
Qed.

(* edge 0x0308 -> 0x026c: integer field 10 is a list *)
Lemma parentHeaderEdgeError_0308_026c (args : ParentHeaderArgs) (returnAddress : Z) (call12_after : DecodeItemOutcome) (call12_kept_x18 : bv 64) (call12_kept_x20 : bv 64) (call11_kept_x19 : bv 64) (call10_after : DecodeItemOutcome) (call_after : DecodeItemOutcome) :
  (bv_unsigned (parentHeaderReturnAddress args) = returnAddress /\ parentHeaderArgsWellFormed args) ->
  Pilot0308Entries.fp_machineAt0308_ForwardA0N0_Hist args returnAddress call12_after call12_kept_x18 call12_kept_x20 call11_kept_x19 call10_after call_after ->
  bv_unsigned (bv_and (bv_zero_extend 64 (List.nth 16 call12_after (BV 8 0))) (BV 64 1)) <> 0 ->
  candidateParentHeader (parentHeaderInputBytes args) = candidateHeaderError.
Proof.
  intros [_ Hwf] Hh Hg.
  unfold Pilot0308Entries.fp_machineAt0308_ForwardA0N0_Hist, ZesuSsz.Automation2.Hist.zesu_join_history in Hh. decompose [ex and] Hh.
  eapply (phIntegerReject _ 10 _ _ call12_kept_x18 call12_kept_x20); [left; exact Hg|eassumption|eassumption|reflexivity..|].
  repeat first [eapply phRegsRenameP; [eassumption|] | eapply phRegsRenameL; [eassumption|]
    | eapply phRegsStart; eassumption
    | eapply phRegsAdvance; [eassumption|reflexivity|first [left; reflexivity | right; assumption | right; eapply phNamedNonzero; eassumption | right; apply walkRemainingNonzero; assumption]|]
    | eapply phRegsNext; [eassumption..|reflexivity|reflexivity|first [assumption | eapply phNamedNonzero; eassumption | apply walkRemainingNonzero; assumption]|]].
Qed.

(* edge 0x0314 -> 0x026c: integer field 10 is longer than 8 bytes *)
Lemma parentHeaderEdgeError_0314_026c (args : ParentHeaderArgs) (returnAddress : Z) (call12_after : DecodeItemOutcome) (call12_kept_x18 : bv 64) (call12_kept_x20 : bv 64) (call11_kept_x19 : bv 64) (call10_after : DecodeItemOutcome) (call_after : DecodeItemOutcome) :
  (bv_unsigned (parentHeaderReturnAddress args) = returnAddress /\ parentHeaderArgsWellFormed args) ->
  Pilot0314Entries.fp_machineAt0314_ForwardA0N0_Hist args returnAddress call12_after call12_kept_x18 call12_kept_x20 call11_kept_x19 call10_after call_after ->
  8 < bv_unsigned (listWord64At8 call12_after) ->
  candidateParentHeader (parentHeaderInputBytes args) = candidateHeaderError.
Proof.
  intros [_ Hwf] Hh Hg.
  unfold Pilot0314Entries.fp_machineAt0314_ForwardA0N0_Hist, ZesuSsz.Automation2.Hist.zesu_join_history in Hh. decompose [ex and] Hh.
  eapply (phIntegerReject _ 10 _ _ call12_kept_x18 call12_kept_x20); [right; exact Hg|eassumption|eassumption|reflexivity..|].
  repeat first [eapply phRegsRenameP; [eassumption|] | eapply phRegsRenameL; [eassumption|]
    | eapply phRegsStart; eassumption
    | eapply phRegsAdvance; [eassumption|reflexivity|first [left; reflexivity | right; assumption | right; eapply phNamedNonzero; eassumption | right; apply walkRemainingNonzero; assumption]|]
    | eapply phRegsNext; [eassumption..|reflexivity|reflexivity|first [assumption | eapply phNamedNonzero; eassumption | apply walkRemainingNonzero; assumption]|]].
Qed.

(* edge 0x0368 -> 0x026c: field 11's decodeItem call fails *)
Lemma parentHeaderEdgeError_0368_026c (args : ParentHeaderArgs) (returnAddress : Z) (call12_after : DecodeItemOutcome) (call12_kept_x18 : bv 64) (call12_kept_x20 : bv 64) (call10_after : DecodeItemOutcome) (call_after : DecodeItemOutcome) (call13_after : DecodeItemOutcome) (call13_kept_x18 : bv 64) (call13_kept_x19 : bv 64) :
  (bv_unsigned (parentHeaderReturnAddress args) = returnAddress /\ parentHeaderArgsWellFormed args) ->
  zesu_named_eq call13_kept_x18 (bv_sub call12_kept_x20 (listWord64At24 call12_after)) ->
  zesu_named_eq call13_kept_x19 (bv_add call12_kept_x18 (listWord64At24 call12_after)) ->
  phCallMeaning args call13_kept_x19 call13_kept_x18 call13_after ->
  Pilot0368Entries.fp_machineAt0368_ForwardA0N0_Hist args returnAddress call12_after call12_kept_x18 call12_kept_x20 call10_after call_after ->
  bv_unsigned (bv_concat 16 (List.nth 33 call13_after (BV 8 0)) (List.nth 32 call13_after (BV 8 0))) <> 0 ->
  candidateParentHeader (parentHeaderInputBytes args) = candidateHeaderError.
Proof.
  intros [_ Hwf] ? ? (? & ? & ? & ? & ? & ?) Hh Hg.
  unfold Pilot0368Entries.fp_machineAt0368_ForwardA0N0_Hist, ZesuSsz.Automation2.Hist.zesu_join_history in Hh. decompose [ex and] Hh.
  eapply (phFieldError _ 11 _ _ call13_kept_x19 call13_kept_x18); [exact Hg|eassumption|reflexivity|first [left; reflexivity | right; assumption | right; eapply phNamedNonzero; eassumption | right; apply walkRemainingNonzero; assumption]|].
  repeat first [eapply phRegsRenameP; [eassumption|] | eapply phRegsRenameL; [eassumption|]
    | eapply phRegsStart; eassumption
    | eapply phRegsAdvance; [eassumption|reflexivity|first [left; reflexivity | right; assumption | right; eapply phNamedNonzero; eassumption | right; apply walkRemainingNonzero; assumption]|]
    | eapply phRegsNext; [eassumption..|reflexivity|reflexivity|first [assumption | eapply phNamedNonzero; eassumption | apply walkRemainingNonzero; assumption]|]].
Qed.

(* edge 0x0370 -> 0x026c: integer field 11 is a list *)
Lemma parentHeaderEdgeError_0370_026c (args : ParentHeaderArgs) (returnAddress : Z) (call13_after : DecodeItemOutcome) (call13_kept_x18 : bv 64) (call13_kept_x19 : bv 64) (call12_after : DecodeItemOutcome) (call12_kept_x18 : bv 64) (call12_kept_x20 : bv 64) (call10_after : DecodeItemOutcome) (call_after : DecodeItemOutcome) :
  (bv_unsigned (parentHeaderReturnAddress args) = returnAddress /\ parentHeaderArgsWellFormed args) ->
  Pilot0370Entries.fp_machineAt0370_ForwardA0N0_Hist args returnAddress call13_after call13_kept_x18 call13_kept_x19 call12_after call12_kept_x18 call12_kept_x20 call10_after call_after ->
  bv_unsigned (bv_and (bv_zero_extend 64 (List.nth 16 call13_after (BV 8 0))) (BV 64 1)) <> 0 ->
  candidateParentHeader (parentHeaderInputBytes args) = candidateHeaderError.
Proof.
  intros [_ Hwf] Hh Hg.
  unfold Pilot0370Entries.fp_machineAt0370_ForwardA0N0_Hist, ZesuSsz.Automation2.Hist.zesu_join_history in Hh. decompose [ex and] Hh.
  eapply (phIntegerReject _ 11 _ _ call13_kept_x19 call13_kept_x18); [left; exact Hg|eassumption|eassumption|reflexivity..|].
  repeat first [eapply phRegsRenameP; [eassumption|] | eapply phRegsRenameL; [eassumption|]
    | eapply phRegsStart; eassumption
    | eapply phRegsAdvance; [eassumption|reflexivity|first [left; reflexivity | right; assumption | right; eapply phNamedNonzero; eassumption | right; apply walkRemainingNonzero; assumption]|]
    | eapply phRegsNext; [eassumption..|reflexivity|reflexivity|first [assumption | eapply phNamedNonzero; eassumption | apply walkRemainingNonzero; assumption]|]].
Qed.

(* edge 0x037c -> 0x026c: integer field 11 is longer than 8 bytes *)
Lemma parentHeaderEdgeError_037c_026c (args : ParentHeaderArgs) (returnAddress : Z) (call13_after : DecodeItemOutcome) (call13_kept_x18 : bv 64) (call13_kept_x19 : bv 64) (call12_after : DecodeItemOutcome) (call12_kept_x18 : bv 64) (call12_kept_x20 : bv 64) (call10_after : DecodeItemOutcome) (call_after : DecodeItemOutcome) :
  (bv_unsigned (parentHeaderReturnAddress args) = returnAddress /\ parentHeaderArgsWellFormed args) ->
  Pilot037cEntries.fp_machineAt037c_ForwardA0N0_Hist args returnAddress call13_after call13_kept_x18 call13_kept_x19 call12_after call12_kept_x18 call12_kept_x20 call10_after call_after ->
  8 < bv_unsigned (listWord64At8 call13_after) ->
  candidateParentHeader (parentHeaderInputBytes args) = candidateHeaderError.
Proof.
  intros [_ Hwf] Hh Hg.
  unfold Pilot037cEntries.fp_machineAt037c_ForwardA0N0_Hist, ZesuSsz.Automation2.Hist.zesu_join_history in Hh. decompose [ex and] Hh.
  eapply (phIntegerReject _ 11 _ _ call13_kept_x19 call13_kept_x18); [right; exact Hg|eassumption|eassumption|reflexivity..|].
  repeat first [eapply phRegsRenameP; [eassumption|] | eapply phRegsRenameL; [eassumption|]
    | eapply phRegsStart; eassumption
    | eapply phRegsAdvance; [eassumption|reflexivity|first [left; reflexivity | right; assumption | right; eapply phNamedNonzero; eassumption | right; apply walkRemainingNonzero; assumption]|]
    | eapply phRegsNext; [eassumption..|reflexivity|reflexivity|first [assumption | eapply phNamedNonzero; eassumption | apply walkRemainingNonzero; assumption]|]].
Qed.
