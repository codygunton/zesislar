(* Step 2.4 M1: the edge obligations of decodeParentHeader's error joins
   0x0088, 0x00a8, 0x00b0, 0x026c, 0x0270 and 0x0408.
   Owner: compliance proof (hand-written). Each generated declaration
   `fp_edge<src>_<join>_CandidateError` (Generated/DecodeParentHeader/FP301/
   EdgeObligations.v) states: the source block's history, its visible facts
   and the edge's own guards imply
   `candidateParentHeader (parentHeaderInputBytes args) = candidateHeaderError`.
   The rendered edge instance (Edges<src>.v) applies `<declaration>_holds`,
   so the join's history holds why the result is an error. Every proof is
   the tactic of ParentHeaderEdgeTactic.v with the failing field's terminal
   (ParentHeaderCandidateFacts.v). *)
From Coq Require Import List ZArith.
From stdpp Require Import base bitvector.definitions.
Require Import ZesuSsz.Contracts.Candidates.ParentHeaderCandidate.
Require Import ZesuSsz.Contracts.ParentHeaderCandidateWalk.
Require Import ZesuSsz.Compliance.ParentHeaderCandidateFacts.
Require Import ZesuSsz.Compliance.ParentHeaderEdgeTactic.
Require Import ZesuSsz.Generated.DecodeParentHeader.FP301.EdgeObligations.

(* 0x00a8 and 0x00b0: the outer item *)
Lemma fp_edge0048_00b0_CandidateError_holds : fp_edge0048_00b0_CandidateError.
Proof. ph_edge_error candidateOuterDecodeError. Qed.
Lemma fp_edge0094_00b0_CandidateError_holds : fp_edge0094_00b0_CandidateError.
Proof. ph_edge_error candidateOuterNotList. Qed.
Lemma fp_edge0060_00a8_CandidateError_holds : fp_edge0060_00a8_CandidateError.
Proof. ph_edge_error candidateOuterEmpty. Qed.

(* 0x00a8: nothing left before a required field *)
Lemma fp_edge00a0_00a8_CandidateError_holds : fp_edge00a0_00a8_CandidateError.
Proof. ph_edge_error (phMissingNext _ 0 _ _ call2_kept_x19 call2_kept_x18 call2_after). Qed.
Lemma fp_edge0110_00a8_CandidateError_holds : fp_edge0110_00a8_CandidateError.
Proof. ph_edge_error (phMissingNext _ 1 _ _ call3_kept_x19 call3_kept_x18 call3_after). Qed.
Lemma fp_edge013c_00a8_CandidateError_holds : fp_edge013c_00a8_CandidateError.
Proof. ph_edge_error (phMissingNext _ 2 _ _ call4_kept_x19 call4_kept_x18 call4_after). Qed.
Lemma fp_edge0168_00a8_CandidateError_holds : fp_edge0168_00a8_CandidateError.
Proof. ph_edge_error (phMissingNext _ 3 _ _ call5_kept_x19 call5_kept_x18 call5_after). Qed.
Lemma fp_edge0194_00a8_CandidateError_holds : fp_edge0194_00a8_CandidateError.
Proof. ph_edge_error (phMissingNext _ 4 _ _ call6_kept_x19 call6_kept_x18 call6_after). Qed.
Lemma fp_edge01c0_00a8_CandidateError_holds : fp_edge01c0_00a8_CandidateError.
Proof. ph_edge_error (phMissingNext _ 5 _ _ call7_kept_x19 call7_kept_x18 call7_after). Qed.
Lemma fp_edge01ec_00a8_CandidateError_holds : fp_edge01ec_00a8_CandidateError.
Proof. ph_edge_error (phMissingNext _ 6 _ _ call8_kept_x19 call8_kept_x18 call8_after). Qed.
Lemma fp_edge0218_00a8_CandidateError_holds : fp_edge0218_00a8_CandidateError.
Proof. ph_edge_error (phMissingNext _ 7 _ _ call9_kept_x19 call9_kept_x18 call9_after). Qed.

(* 0x0088: a skipped field's item does not decode *)
Lemma fp_edge0080_0088_CandidateError_holds : fp_edge0080_0088_CandidateError.
Proof. ph_edge_error (phFieldError _ 0 _ _ call2_kept_x19 call2_kept_x18). Qed.
Lemma fp_edge0108_0088_CandidateError_holds : fp_edge0108_0088_CandidateError.
Proof. ph_edge_error (phFieldError _ 1 _ _ call3_kept_x19 call3_kept_x18). Qed.
Lemma fp_edge0134_0088_CandidateError_holds : fp_edge0134_0088_CandidateError.
Proof. ph_edge_error (phFieldError _ 2 _ _ call4_kept_x19 call4_kept_x18). Qed.
Lemma fp_edge0160_0088_CandidateError_holds : fp_edge0160_0088_CandidateError.
Proof. ph_edge_error (phFieldError _ 3 _ _ call5_kept_x19 call5_kept_x18). Qed.
Lemma fp_edge018c_0088_CandidateError_holds : fp_edge018c_0088_CandidateError.
Proof. ph_edge_error (phFieldError _ 4 _ _ call6_kept_x19 call6_kept_x18). Qed.
Lemma fp_edge01b8_0088_CandidateError_holds : fp_edge01b8_0088_CandidateError.
Proof. ph_edge_error (phFieldError _ 5 _ _ call7_kept_x19 call7_kept_x18). Qed.
Lemma fp_edge01e4_0088_CandidateError_holds : fp_edge01e4_0088_CandidateError.
Proof. ph_edge_error (phFieldError _ 6 _ _ call8_kept_x19 call8_kept_x18). Qed.
Lemma fp_edge0210_0088_CandidateError_holds : fp_edge0210_0088_CandidateError.
Proof. ph_edge_error (phFieldError _ 7 _ _ call9_kept_x19 call9_kept_x18). Qed.
Lemma fp_edge023c_0088_CandidateError_holds : fp_edge023c_0088_CandidateError.
Proof. ph_edge_error (phFieldError _ 8 _ _ call10_kept_x19 call10_kept_x20). Qed.

(* 0x026c: an integer field (9 to 11) does not decode, is a list or is wider than 8 bytes *)
Lemma fp_edge0264_026c_CandidateError_holds : fp_edge0264_026c_CandidateError.
Proof. ph_edge_error (phFieldError _ 9 _ _ call11_kept_x18 call11_kept_x19). Qed.
Lemma fp_edge02a4_026c_CandidateError_holds : fp_edge02a4_026c_CandidateError.
Proof. ph_edge_error (phIntegerReject _ 9 _ _ call11_kept_x18 call11_kept_x19 _ _ _ _ _ call11_after). Qed.
Lemma fp_edge02b0_026c_CandidateError_holds : fp_edge02b0_026c_CandidateError.
Proof. ph_edge_error (phIntegerReject _ 9 _ _ call11_kept_x18 call11_kept_x19 _ _ _ _ _ call11_after). Qed.
Lemma fp_edge0300_026c_CandidateError_holds : fp_edge0300_026c_CandidateError.
Proof. ph_edge_error (phFieldError _ 10 _ _ call12_kept_x18 call12_kept_x20). Qed.
Lemma fp_edge0308_026c_CandidateError_holds : fp_edge0308_026c_CandidateError.
Proof. ph_edge_error (phIntegerReject _ 10 _ _ call12_kept_x18 call12_kept_x20 _ _ _ _ _ call12_after). Qed.
Lemma fp_edge0314_026c_CandidateError_holds : fp_edge0314_026c_CandidateError.
Proof. ph_edge_error (phIntegerReject _ 10 _ _ call12_kept_x18 call12_kept_x20 _ _ _ _ _ call12_after). Qed.
Lemma fp_edge0368_026c_CandidateError_holds : fp_edge0368_026c_CandidateError.
Proof. ph_edge_error (phFieldError _ 11 _ _ call13_kept_x19 call13_kept_x18). Qed.
Lemma fp_edge0370_026c_CandidateError_holds : fp_edge0370_026c_CandidateError.
Proof. ph_edge_error (phIntegerReject _ 11 _ _ call13_kept_x19 call13_kept_x18 _ _ _ _ _ call13_after). Qed.
Lemma fp_edge037c_026c_CandidateError_holds : fp_edge037c_026c_CandidateError.
Proof. ph_edge_error (phIntegerReject _ 11 _ _ call13_kept_x19 call13_kept_x18 _ _ _ _ _ call13_after). Qed.

(* 0x0408: a skipped field 12 to 14 does not decode *)
Lemma fp_edge0400_0408_CandidateError_holds : fp_edge0400_0408_CandidateError.
Proof. ph_edge_error (phFieldError _ 12 _ _ call14_kept_x19 call14_kept_x18). Qed.
Lemma fp_edge0438_0408_CandidateError_holds : fp_edge0438_0408_CandidateError.
Proof. ph_edge_error (phFieldError _ 13 _ _ call15_kept_x19 call15_kept_x18). Qed.
Lemma fp_edge0464_0408_CandidateError_holds : fp_edge0464_0408_CandidateError.
Proof. ph_edge_error (phFieldError _ 14 _ _ call16_kept_x19 call16_kept_x18). Qed.

(* 0x00b0 and 0x0270: field 16 does not decode; the nextUint64 call of field 15, 17 or 18 fails *)
Lemma fp_edge04ec_00b0_CandidateError_holds : fp_edge04ec_00b0_CandidateError.
Proof. ph_edge_error (phFieldError _ 16 _ _ call17_word_1_0 call17_word_1_8). Qed.
Lemma fp_edge04a8_0270_CandidateError_holds : fp_edge04a8_0270_CandidateError.
Proof.
  ph_edge_error (phNextReject _ 15 _ _ (bv_add call16_kept_x19 (listWord64At24 call16_after))
    (bv_sub call16_kept_x18 (listWord64At24 call16_after))).
Qed.
Lemma fp_edge0568_0270_CandidateError_holds : fp_edge0568_0270_CandidateError.
Proof.
  ph_edge_error (phNextReject _ 17 _ _ (bv_add call17_word_1_0 (listWord64At24 call18_after))
    (bv_sub call17_word_1_8 (listWord64At24 call18_after))).
Qed.
Lemma fp_edge059c_0270_CandidateError_holds : fp_edge059c_0270_CandidateError.
Proof. ph_edge_error (phNextReject _ 18 _ _ call20_arg_word_1_0 call20_arg_word_1_8). Qed.
