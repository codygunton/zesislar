(* Step 2.4 M1: the meaning of decodeParentHeader's success exits (slots 1 to
   6 of the return block 0x0274), from the histories of their return
   packages, with no hypothesis. Owner: compliance proof (hand-written).

   Every package history carries the walk facts of the return sites
   (`ParentHeaderWalkFact.v`, amendment 14) up to field 14 (return site
   0x0464) and, after it, the records and guards of the calls since:
   - slot 1: the join 0x03bc holds the candidate's success with the three
     stored words (each incoming edge proves it, obligation CandidateSuccess);
   - slot 4: field 14 consumed everything left;
   - slots 5, 6, 2, 3: field 14 left something, field 15 (nextUint64) gave the
     base fee; then nothing left (5), field 16 consumed everything (6),
     field 17 gave the blob gas and nothing was left (2), field 18 gave the
     excess blob gas (3).
   0x0510 and 0x0514 are duplicated joins (one entry per path), so each
   package holds exactly its own path's facts. The candidate's header then
   follows by a few step lemmas, and the stored bytes are
   parentHeaderSuccessBytes with each option's record. *)
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
Require Import ZesuSsz.Contracts.ParentHeaderWalkFact.
Require Import ZesuSsz.Compliance.ParentHeaderEdgeTactic.
Require Import ZesuSsz.Compliance.ParentHeaderWalkTactic.
Require Import ZesuSsz.Contracts.ParentHeader.
Require Import ZesuSsz.Contracts.NextUint64CallData.
Require Import ZesuSsz.Interfaces.NextUint64.
Require ZesuSsz.Generated.DecodeParentHeader.FP301.FunctionReturnEntries.

Import ListNotations.
Open Scope Z_scope.

(* ---- Slot 1: the join 0x03bc (nothing left before field 12, 13 or 14:
   edges from 0x03b0, 0x0414, 0x0440) -> 0x0274; three zero records. Every
   edge into the join proves the candidate's success with the three stored
   words (obligation CandidateSuccess); the package keeps it in its
   history. ---- *)

(* An opened package history: every group, existential and conjunction. *)
Ltac ph_history_open :=
  repeat match goal with
  | H : _ /\ _ |- _ => destruct H
  | H : ex _ |- _ => destruct H
  | H : zesu_join_history _ |- _ => unfold zesu_join_history in H
  end.

(* The named registers [x], [y] replaced by their definitions. *)
Ltac ph_history_names x y :=
  repeat match goal with
  | H : zesu_named_eq x _ |- _ => destruct H as [H]
  | H : zesu_named_eq y _ |- _ => destruct H as [H]
  end;
  subst x y.

(* The join's success fact, read from an opened package history. *)
Ltac ph_history_success :=
  match goal with H : zesu_hist _ |- _ => apply zesu_hist_elim in H; hnf in H end;
  ph_history_open;
  match goal with H : candidateParentHeader _ = candidateHeaderSuccess _ |- _ => exact H end.

Lemma parentHeaderSlot1ExitMeaning_holds :
  FunctionReturnEntries.fp_machineReturn_slot1_ForwardA0N0_ExitMeaning parentHeaderResultMeaning.
Proof.
  intros args returnAddress call13_after call10_after call_after machine_x21_1 machine_x22_1
    machine_x10 machine_x20_1 join_bytes unwritten_74 Hh [_ Hwf]; intros.
  change (FunctionReturnEntries.fp_machineReturn_slot1_ForwardA0N0_ResultBytes args returnAddress
      machine_x21_1 machine_x22_1 machine_x20_1 unwritten_74)
    with (parentHeaderSuccessBytes machine_x21_1 machine_x22_1 machine_x20_1
      parentHeaderZeroRecord parentHeaderZeroRecord parentHeaderZeroRecord unwritten_74).
  apply parentHeaderMeaningOfCandidateWellFormed; [exact Hwf|].
  apply parentHeaderNoOptionResult; [ph_history_success|assumption].
Qed.

(* ---- Slot 4: fields 12 to 14 consumed, nothing left before field 15
   (0x0488 -> 0x048c -> 0x0514 -> 0x0274); the three records are copied
   from the None constant (sixteen zero bytes) ---- *)

Lemma parentHeaderSlot4Bytes args returnAddress (machine_x21_1 machine_x22_1 machine_x20_1 : bv 64)
    unwritten_74 :
  FunctionReturnEntries.fp_machineReturn_slot4_ForwardA0N0_ResultBytes args returnAddress
    machine_x21_1 machine_x22_1 machine_x20_1 unwritten_74 =
  parentHeaderSuccessBytes machine_x21_1 machine_x22_1 machine_x20_1
    parentHeaderZeroRecord parentHeaderZeroRecord parentHeaderZeroRecord unwritten_74.
Proof.
  unfold FunctionReturnEntries.fp_machineReturn_slot4_ForwardA0N0_ResultBytes,
    parentHeaderSuccessBytes, parentHeaderWordBytes, parentHeaderZeroRecord.
  cbn [app].
  repeat (apply (f_equal2 cons); [first [reflexivity | apply bv_eq; vm_compute; reflexivity] |]).
  reflexivity.
Qed.

(* The package history holds the walk fact before field 14 (return site
   0x0464), the record of call 16 (field 14) on that window, its success
   status and the guard "nothing left" (the window length equals the bytes
   call 16 consumed). Field 15 is optional: the candidate accepts with the
   three stored words. *)
Lemma parentHeaderSlot4ExitMeaning_holds :
  FunctionReturnEntries.fp_machineReturn_slot4_ForwardA0N0_ExitMeaning parentHeaderResultMeaning.
Proof.
  intros args returnAddress call16_after call16_kept_x18 call16_kept_x19 call13_after call10_after
    call_after machine_x21_1 machine_x22_1 machine_x20_1 unwritten_74 Hh [_ Hwf]; intros.
  rewrite parentHeaderSlot4Bytes.
  apply parentHeaderMeaningOfCandidateWellFormed; [exact Hwf|].
  apply parentHeaderNoOptionResult; [|assumption].
  apply zesu_hist_elim in Hh; hnf in Hh; ph_history_open.
  match goal with H : parentHeaderWalkSkipped _ 14 _ _ _ _ |- _ => unfold parentHeaderWalkSkipped in H end.
  ph_history_names call16_kept_x18 call16_kept_x19.
  match goal with H : bv_unsigned (bv_sub _ _) = bv_unsigned (bv_concat 64 _ (nth 24 call16_after _)) |- _ =>
    apply bv_eq in H end.
  match goal with H : parentHeaderWalkAt _ 14 _ _ _ |- _ =>
    refine (parentHeaderSuccessAfterSkip _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ H _ _ _) end;
  first [ reflexivity | eapply parentHeaderCallC1B; eassumption | eassumption ].
Qed.

(* ---- Fields 14 (skip) and 15 (base fee, nextUint64), shared by the
   slots with options (5, 6, 2, 3). From the walk fact before field 14
   (return site 0x0464), call 16's record on that window, its status, the
   guard "something left" after it, and call 17's (nextUint64) record on the
   rest with its status and rest words: the walk before field 16. ---- *)

Lemma phWalkBaseFee args (p15 l15 : bv 64) (a15 : DecodeItemOutcome) acc (p16 l16 : bv 64)
    a0 rest sp inputEnd before16 after16 argv sp' inputEnd' ret (w0 w8 : bv 64) :
  parentHeaderWalkSkipped args 14 p15 l15 a15 acc ->
  zesu_named_eq l16 (bv_sub l15 (listWord64At24 a15)) ->
  zesu_named_eq p16 (bv_add p15 (listWord64At24 a15)) ->
  decodeItemCallMeaning (decodeItemCallDataArgs (a0 :: p16 :: rest) sp inputEnd
    (take (Z.to_nat (bv_unsigned l16))
      (drop (Z.to_nat (bv_unsigned p16 - bv_unsigned (parentHeaderInputPointer args)))
        (parentHeaderInputBytes args))) before16) after16 ->
  bv_unsigned (bv_concat 16 (List.nth 33 after16 (BV 8 0)) (List.nth 32 after16 (BV 8 0))) = 0 ->
  bv_unsigned l16 <> bv_unsigned (listWord64At24 after16) ->
  nextUint64CallResult (nextUint64Base (nextUint64CallDataArgs argv sp'
    (bv_add p16 (listWord64At24 after16)) inputEnd'
    (take (Z.to_nat (bv_unsigned (bv_sub l16 (listWord64At24 after16))))
      (drop (Z.to_nat (bv_unsigned (bv_add p16 (listWord64At24 after16)) -
                       bv_unsigned (parentHeaderInputPointer args)))
        (parentHeaderInputBytes args))))) ret ->
  w0 = Z_to_bv 64 (nextRestPointer ret) ->
  w8 = Z_to_bv 64 (nextRestLength ret) ->
  bv_unsigned (bv_concat 16 (List.nth 9 (nextResultBytes ret) (BV 8 0))
    (List.nth 8 (nextResultBytes ret) (BV 8 0))) = 0 ->
  parentHeaderWalkState args 16 w0 w8 (acc ++ [bv_unsigned (listWord64At0 (nextResultBytes ret))]).
Proof.
  intros Hw [El] [Ep] Hm Hok Hleft Hr H0 H8 Hok17. subst l16 p16.
  unfold parentHeaderWalkSkipped in Hw.
  assert (H15 := parentHeaderWalkSkipOf args 14 _ _ _ _ acc _ after16 eq_refl eq_refl Hw
    (parentHeaderCallC1B _ _ _ _ _ _ _ _ Hm) Hok ltac:(intros E; apply Hleft; rewrite E; reflexivity)).
  unfold parentHeaderWalkSkipped in H15.
  refine (parentHeaderWalkNextOf args 15 _ _ _ _ _ _ acc _ ret eq_refl eq_refl H15 _ _
    (parentHeaderNextUint64Root _ _ Hr) Hok17 H0 H8); reflexivity.
Qed.

(* ---- One step each, on the registers of the histories (fields 16 to 18) ---- *)

Lemma phStateLeft args k (p l : bv 64) acc :
  parentHeaderWalkState args k p l acc -> bv_unsigned l <> 0 -> parentHeaderWalkAt args k p l acc.
Proof. intros Hs Hl. split; [exact Hs|exact Hl]. Qed.

(* A skipped field with something left after it. *)
Lemma phSkipLeft args k pc kind (p l : bv 64) acc a0 rest sp inputEnd before after :
  nth_error parentHeaderFieldSchedule k = Some (pc, kind) ->
  parentHeaderFieldIsInteger kind = false ->
  parentHeaderWalkAt args k p l acc ->
  decodeItemCallMeaning (decodeItemCallDataArgs (a0 :: p :: rest) sp inputEnd
    (take (Z.to_nat (bv_unsigned l))
      (drop (Z.to_nat (bv_unsigned p - bv_unsigned (parentHeaderInputPointer args)))
        (parentHeaderInputBytes args))) before) after ->
  bv_unsigned (bv_concat 16 (List.nth 33 after (BV 8 0)) (List.nth 32 after (BV 8 0))) = 0 ->
  bv_unsigned l <> bv_unsigned (listWord64At24 after) ->
  parentHeaderWalkAt args (S k) (bv_add p (listWord64At24 after)) (bv_sub l (listWord64At24 after)) acc.
Proof.
  intros Hk Hint Hw Hm Hok Hleft.
  exact (parentHeaderWalkSkipOf _ _ _ _ _ _ _ _ _ Hk Hint Hw (parentHeaderCallC1B _ _ _ _ _ _ _ _ Hm) Hok
    ltac:(intros E; apply Hleft; rewrite E; reflexivity)).
Qed.

(* A skipped field that consumed everything left, before an optional field. *)
Lemma phSkipDone args k pc kind pc' kind' (p l : bv 64) acc a0 rest sp inputEnd before after :
  nth_error parentHeaderFieldSchedule k = Some (pc, kind) ->
  parentHeaderFieldIsInteger kind = false ->
  nth_error parentHeaderFieldSchedule (S k) = Some (pc', kind') ->
  parentHeaderFieldIsRequired kind' = false ->
  parentHeaderWalkAt args k p l acc ->
  decodeItemCallMeaning (decodeItemCallDataArgs (a0 :: p :: rest) sp inputEnd
    (take (Z.to_nat (bv_unsigned l))
      (drop (Z.to_nat (bv_unsigned p - bv_unsigned (parentHeaderInputPointer args)))
        (parentHeaderInputBytes args))) before) after ->
  bv_unsigned (bv_concat 16 (List.nth 33 after (BV 8 0)) (List.nth 32 after (BV 8 0))) = 0 ->
  bv_unsigned l = bv_unsigned (listWord64At24 after) ->
  candidateParentHeader (parentHeaderInputBytes args) = candidateHeaderSuccess (candidateHeaderOfValues acc).
Proof.
  intros Hk Hint Hk' Hopt Hw Hm Hok Hnone.
  exact (parentHeaderSuccessAfterSkip _ _ _ _ _ _ _ _ _ _ _ Hk Hint Hk' Hopt Hw
    (parentHeaderCallC1B _ _ _ _ _ _ _ _ Hm) Hok (proj2 (bv_eq _ _ _) Hnone)).
Qed.

(* An optional integer field through nextUint64 whose window registers are
   named equal to the walk's. *)
Lemma phNextNamed args k pc kind (p l p' l' w0 w8 : bv 64) acc argv sp inputEnd ret :
  nth_error parentHeaderFieldSchedule k = Some (pc, kind) ->
  parentHeaderFieldIsInteger kind = true ->
  parentHeaderWalkAt args k p l acc ->
  zesu_named_eq p' p ->
  zesu_named_eq l' l ->
  nextUint64CallResult (nextUint64Base (nextUint64CallDataArgs argv sp p' inputEnd
    (take (Z.to_nat (bv_unsigned l'))
      (drop (Z.to_nat (bv_unsigned p' - bv_unsigned (parentHeaderInputPointer args)))
        (parentHeaderInputBytes args))))) ret ->
  w0 = Z_to_bv 64 (nextRestPointer ret) ->
  w8 = Z_to_bv 64 (nextRestLength ret) ->
  bv_unsigned (bv_concat 16 (List.nth 9 (nextResultBytes ret) (BV 8 0))
    (List.nth 8 (nextResultBytes ret) (BV 8 0))) = 0 ->
  parentHeaderWalkState args (S k) w0 w8 (acc ++ [bv_unsigned (listWord64At0 (nextResultBytes ret))]).
Proof.
  intros Hk Hint Hw [->] [->] Hr H0 H8 Hok.
  refine (parentHeaderWalkNextOf _ _ _ _ _ _ _ _ _ _ _ Hk Hint Hw _ _
    (parentHeaderNextUint64Root _ _ Hr) Hok H0 H8); reflexivity.
Qed.

Lemma phNext args k pc kind (p l w0 w8 : bv 64) acc argv sp inputEnd ret :
  nth_error parentHeaderFieldSchedule k = Some (pc, kind) ->
  parentHeaderFieldIsInteger kind = true ->
  parentHeaderWalkAt args k p l acc ->
  nextUint64CallResult (nextUint64Base (nextUint64CallDataArgs argv sp p inputEnd
    (take (Z.to_nat (bv_unsigned l))
      (drop (Z.to_nat (bv_unsigned p - bv_unsigned (parentHeaderInputPointer args)))
        (parentHeaderInputBytes args))))) ret ->
  w0 = Z_to_bv 64 (nextRestPointer ret) ->
  w8 = Z_to_bv 64 (nextRestLength ret) ->
  bv_unsigned (bv_concat 16 (List.nth 9 (nextResultBytes ret) (BV 8 0))
    (List.nth 8 (nextResultBytes ret) (BV 8 0))) = 0 ->
  parentHeaderWalkState args (S k) w0 w8 (acc ++ [bv_unsigned (listWord64At0 (nextResultBytes ret))]).
Proof.
  intros Hk Hint Hw Hr H0 H8 Hok.
  exact (phNextNamed _ _ _ _ _ _ p l _ _ _ _ _ _ _ Hk Hint Hw (zesu_named_eq_intro _ _ eq_refl)
    (zesu_named_eq_intro _ _ eq_refl) Hr H0 H8 Hok).
Qed.

(* The tag word of a present record as the return block reads it: seven
   uninitialised bytes above the tag byte 1. *)
Definition phTagWord (u1 u2 u3 u4 u5 u6 u7 : bv 8) : bv 64 :=
  bv_concat 64 (bv_concat 56 (bv_concat 48 (bv_concat 40 (bv_concat 32 (bv_concat 24
    (bv_concat 16 u1 u2) u3) u4) u5) u6) u7) (BV 8 1).

(* A package's stored bytes, byte by byte, against parentHeaderSuccessBytes. *)
Ltac ph_result_bytes :=
  unfold parentHeaderSuccessBytes, parentHeaderPresentRecord, parentHeaderWordBytes,
    parentHeaderZeroRecord, phTagWord;
  cbn [app];
  repeat (apply (f_equal2 cons); [first [reflexivity | apply bv_eq; vm_compute; reflexivity] |]);
  reflexivity.

(* The success result of a slot whose candidate header is [candidateHeaderOfValues]
   of the walk's values: words, then each option record. *)
Ltac ph_option_result Hc :=
  eapply parentHeaderSuccessResult;
  [ exact Hc | reflexivity | reflexivity | reflexivity
  | first [ exact parentHeaderNoOptionRecord
          | apply parentHeaderPresentRecordOption; try unfold phTagWord; apply parentHeaderTagWordOne ]
  | first [ exact parentHeaderNoOptionRecord
          | apply parentHeaderPresentRecordOption; try unfold phTagWord; apply parentHeaderTagWordOne ]
  | first [ exact parentHeaderNoOptionRecord
          | apply parentHeaderPresentRecordOption; try unfold phTagWord; apply parentHeaderTagWordOne ]
  | assumption ].

(* ---- Slot 5: base fee present, nothing left before field 16
   (0x04c8 -> 0x0510 -> 0x0514 -> 0x0274) ---- *)

Lemma parentHeaderSlot5Bytes args returnAddress call17_result (machine_x21_1 machine_x22_1 machine_x20_1 : bv 64)
    u1 u2 u3 u4 u5 u6 u7 unwritten_74 :
  FunctionReturnEntries.fp_machineReturn_slot5_ForwardA0N0_ResultBytes args returnAddress call17_result
    machine_x21_1 machine_x22_1 machine_x20_1 u1 u2 u3 u4 u5 u6 u7 unwritten_74 =
  parentHeaderSuccessBytes machine_x21_1 machine_x22_1 machine_x20_1
    (parentHeaderPresentRecord (listWord64At0 (nextResultBytes call17_result))
      (bv_concat 64 (bv_concat 56 (bv_concat 48 (bv_concat 40 (bv_concat 32 (bv_concat 24
        (bv_concat 16 u1 u2) u3) u4) u5) u6) u7) (BV 8 1)))
    parentHeaderZeroRecord parentHeaderZeroRecord unwritten_74.
Proof.
  unfold FunctionReturnEntries.fp_machineReturn_slot5_ForwardA0N0_ResultBytes,
    parentHeaderSuccessBytes, parentHeaderPresentRecord, parentHeaderWordBytes, parentHeaderZeroRecord.
  cbn [app].
  repeat (apply (f_equal2 cons); [first [reflexivity | apply bv_eq; vm_compute; reflexivity] |]).
  reflexivity.
Qed.

Lemma parentHeaderSlot5ExitMeaning_holds :
  FunctionReturnEntries.fp_machineReturn_slot5_ForwardA0N0_ExitMeaning parentHeaderResultMeaning.
Proof.
  intros args returnAddress call17_result call17_word_1_0 call17_word_1_8 call16_after call13_after
    call10_after call_after machine_x21_1 machine_x22_1 machine_x20_1 u1 u2 u3 u4 u5 u6 u7 unwritten_74
    Hh [_ Hwf]; intros.
  rewrite parentHeaderSlot5Bytes.
  apply parentHeaderMeaningOfCandidateWellFormed; [exact Hwf|].
  apply zesu_hist_elim in Hh; hnf in Hh; ph_history_open.
  eassert (Ws16 : parentHeaderWalkState args 16 call17_word_1_0 call17_word_1_8 _)
    by (eapply phWalkBaseFee; eassumption).
  assert (Hc := parentHeaderSuccessOfState args 16 _ _ _ _ _ eq_refl eq_refl Ws16 ltac:(eassumption)).
  ph_option_result Hc.
Qed.

(* ---- Slot 6: base fee present, field 16 consumed everything left
   (0x050c -> 0x0510 -> 0x0514 -> 0x0274) ---- *)

Lemma parentHeaderSlot6Bytes args returnAddress call17_result (machine_x21_1 machine_x22_1 machine_x20_1 : bv 64)
    u1 u2 u3 u4 u5 u6 u7 unwritten_74 :
  FunctionReturnEntries.fp_machineReturn_slot6_ForwardA0N0_ResultBytes args returnAddress call17_result
    machine_x21_1 machine_x22_1 machine_x20_1 u1 u2 u3 u4 u5 u6 u7 unwritten_74 =
  parentHeaderSuccessBytes machine_x21_1 machine_x22_1 machine_x20_1
    (parentHeaderPresentRecord (listWord64At0 (nextResultBytes call17_result)) (phTagWord u1 u2 u3 u4 u5 u6 u7))
    parentHeaderZeroRecord parentHeaderZeroRecord unwritten_74.
Proof. unfold FunctionReturnEntries.fp_machineReturn_slot6_ForwardA0N0_ResultBytes. ph_result_bytes. Qed.

Lemma parentHeaderSlot6ExitMeaning_holds :
  FunctionReturnEntries.fp_machineReturn_slot6_ForwardA0N0_ExitMeaning parentHeaderResultMeaning.
Proof.
  intros args returnAddress call18_after call17_result call17_word_1_0 call17_word_1_8 call16_after
    call13_after call10_after call_after machine_x21_1 machine_x22_1 machine_x20_1
    u1 u2 u3 u4 u5 u6 u7 unwritten_74 Hh [_ Hwf]; intros.
  rewrite parentHeaderSlot6Bytes.
  apply parentHeaderMeaningOfCandidateWellFormed; [exact Hwf|].
  apply zesu_hist_elim in Hh; hnf in Hh; ph_history_open.
  eassert (Ws16 : parentHeaderWalkState args 16 call17_word_1_0 call17_word_1_8 _)
    by (eapply phWalkBaseFee; eassumption).
  assert (Wa16 := phStateLeft _ _ _ _ _ Ws16 ltac:(eassumption)).
  eassert (Hc : candidateParentHeader _ = candidateHeaderSuccess _)
    by (eapply (phSkipDone _ 16); [reflexivity|reflexivity|reflexivity|reflexivity|exact Wa16
                                  |eassumption|eassumption|eassumption]).
  ph_option_result Hc.
Qed.

(* ---- Slot 2: base fee and blob gas present, nothing left before field 18
   (0x0588 -> 0x0514 -> 0x0274) ---- *)

Lemma parentHeaderSlot2Bytes args returnAddress call19_result call17_result
    (machine_x21_1 machine_x22_1 machine_x20_1 : bv 64)
    u1 u2 u3 u4 u5 u6 u7 u8 u9 u10 u11 u12 u13 u14 unwritten_74 :
  FunctionReturnEntries.fp_machineReturn_slot2_ForwardA0N0_ResultBytes args returnAddress call19_result
    call17_result machine_x21_1 machine_x22_1 machine_x20_1
    u1 u2 u3 u4 u5 u6 u7 u8 u9 u10 u11 u12 u13 u14 unwritten_74 =
  parentHeaderSuccessBytes machine_x21_1 machine_x22_1 machine_x20_1
    (parentHeaderPresentRecord (listWord64At0 (nextResultBytes call17_result)) (phTagWord u1 u2 u3 u4 u5 u6 u7))
    (parentHeaderPresentRecord (listWord64At0 (nextResultBytes call19_result))
      (phTagWord u8 u9 u10 u11 u12 u13 u14))
    parentHeaderZeroRecord unwritten_74.
Proof. unfold FunctionReturnEntries.fp_machineReturn_slot2_ForwardA0N0_ResultBytes. ph_result_bytes. Qed.

Lemma parentHeaderSlot2ExitMeaning_holds :
  FunctionReturnEntries.fp_machineReturn_slot2_ForwardA0N0_ExitMeaning parentHeaderResultMeaning.
Proof.
  intros args returnAddress call19_result call19_word_1_0 call19_word_1_8 call18_after call17_result
    call16_after call13_after call10_after call_after machine_x21_1 machine_x22_1 machine_x20_1
    u1 u2 u3 u4 u5 u6 u7 u8 u9 u10 u11 u12 u13 u14 unwritten_74 Hh [_ Hwf]; intros.
  rewrite parentHeaderSlot2Bytes.
  apply parentHeaderMeaningOfCandidateWellFormed; [exact Hwf|].
  apply zesu_hist_elim in Hh; hnf in Hh; ph_history_open.
  eassert (Ws16 : parentHeaderWalkState args 16 _ _ _) by (eapply phWalkBaseFee; eassumption).
  assert (Wa16 := phStateLeft _ _ _ _ _ Ws16 ltac:(eassumption)).
  eassert (Wa17 : parentHeaderWalkAt args 17 _ _ _)
    by (eapply (phSkipLeft _ 16); [reflexivity|reflexivity|exact Wa16|eassumption|eassumption|eassumption]).
  eassert (Ws18 : parentHeaderWalkState args 18 call19_word_1_0 call19_word_1_8 _)
    by (eapply (phNext _ 17); [reflexivity|reflexivity|exact Wa17|eassumption|eassumption|eassumption
                              |eassumption]).
  assert (Hc := parentHeaderSuccessOfState args 18 _ _ _ _ _ eq_refl eq_refl Ws18 ltac:(eassumption)).
  ph_option_result Hc.
Qed.

(* ---- Slot 3: all three options (0x05b8 -> 0x0514 -> 0x0274) ---- *)

Lemma parentHeaderSlot3Bytes args returnAddress call20_result call19_result call17_result
    (machine_x21_1 machine_x22_1 machine_x20_1 : bv 64)
    u1 u2 u3 u4 u5 u6 u7 u8 u9 u10 u11 u12 u13 u14 u15 u16 u17 u18 u19 u20 u21 unwritten_74 :
  FunctionReturnEntries.fp_machineReturn_slot3_ForwardA0N0_ResultBytes args returnAddress call20_result
    call19_result call17_result machine_x21_1 machine_x22_1 machine_x20_1
    u1 u2 u3 u4 u5 u6 u7 u8 u9 u10 u11 u12 u13 u14 u15 u16 u17 u18 u19 u20 u21 unwritten_74 =
  parentHeaderSuccessBytes machine_x21_1 machine_x22_1 machine_x20_1
    (parentHeaderPresentRecord (listWord64At0 (nextResultBytes call17_result))
      (phTagWord u8 u9 u10 u11 u12 u13 u14))
    (parentHeaderPresentRecord (listWord64At0 (nextResultBytes call19_result))
      (phTagWord u15 u16 u17 u18 u19 u20 u21))
    (parentHeaderPresentRecord (listWord64At0 (nextResultBytes call20_result)) (phTagWord u1 u2 u3 u4 u5 u6 u7))
    unwritten_74.
Proof. unfold FunctionReturnEntries.fp_machineReturn_slot3_ForwardA0N0_ResultBytes. ph_result_bytes. Qed.

Lemma parentHeaderSlot3ExitMeaning_holds :
  FunctionReturnEntries.fp_machineReturn_slot3_ForwardA0N0_ExitMeaning parentHeaderResultMeaning.
Proof.
  intros args returnAddress call20_result call20_word_1_0 call20_word_1_8 call19_result call18_after
    call17_result call16_after call13_after call10_after call_after machine_x21_1 machine_x22_1
    machine_x20_1 u1 u2 u3 u4 u5 u6 u7 u8 u9 u10 u11 u12 u13 u14 u15 u16 u17 u18 u19 u20 u21
    unwritten_74 Hh [_ Hwf]; intros.
  rewrite parentHeaderSlot3Bytes.
  apply parentHeaderMeaningOfCandidateWellFormed; [exact Hwf|].
  apply zesu_hist_elim in Hh; hnf in Hh; ph_history_open.
  eassert (Ws16 : parentHeaderWalkState args 16 _ _ _) by (eapply phWalkBaseFee; eassumption).
  assert (Wa16 := phStateLeft _ _ _ _ _ Ws16 ltac:(eassumption)).
  eassert (Wa17 : parentHeaderWalkAt args 17 _ _ _)
    by (eapply (phSkipLeft _ 16); [reflexivity|reflexivity|exact Wa16|eassumption|eassumption|eassumption]).
  eassert (Ws18 : parentHeaderWalkState args 18 _ _ _)
    by (eapply (phNext _ 17); [reflexivity|reflexivity|exact Wa17|eassumption|eassumption|eassumption
                              |eassumption]).
  assert (Wa18 := phStateLeft _ _ _ _ _ Ws18 ltac:(eassumption)).
  eassert (Ws19 : parentHeaderWalkState args 19 call20_word_1_0 call20_word_1_8 _)
    by (eapply (phNextNamed _ 18); [reflexivity|reflexivity|exact Wa18|eassumption|eassumption
                                   |eassumption|eassumption|eassumption|eassumption]).
  assert (Hc := candidateWalkDone _ _ _ _ Ws19).
  ph_option_result Hc.
Qed.
