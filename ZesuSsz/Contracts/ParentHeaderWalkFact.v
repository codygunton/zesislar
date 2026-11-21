(* Step 2.4 M1, amendment 14: the walk fact the success path carries.
   Owner: contract fact (definitions over contract predicates and pure step
   lemmas; no generated name, no Iris, no automation).

   [parentHeaderWalkAt args k p l acc]: before field k of the schedule the
   candidate walk stands at the window [p, p + l) of the input with the
   values [acc] (a definite state: the candidate has accepted every earlier
   field), and something is left ([l <> 0]). The return site of each field
   call states it for the window that call was passed, in the history of
   its entry (profile `calls[].return_facts`, history rows):
   [parentHeaderWalkStart args after] for the first field (the outer item's
   payload), [parentHeaderWalkSkipped args k p l after acc] after a skipped
   field whose call had the window [p, p + l) and the outcome [after]. The
   call block's edge into the return site proves it from the previous
   return site's fact (carried in the block's history), that call's record
   and the guards the code took since (status, "something left"). *)
From Coq Require Import List ZArith Lia.
From stdpp Require Import base list numbers bitvector.definitions.
Require Import EvmSailRlp.evm_rlp_types.
Require Import ZesuSsz.Contracts.RlpDecodeItem.
Require Import ZesuSsz.Contracts.ParentHeaderContract.
Require Import ZesuSsz.Contracts.Candidates.ParentHeaderDomain.
Require Import ZesuSsz.Contracts.Candidates.ParentHeaderCandidate.
Require Import ZesuSsz.Contracts.ParentHeaderCandidateWalk.
Require Import ZesuSsz.Automation2.ByteWindowFold.
Require Import ZesuSsz.Automation2.BitvectorFacts.
Require Import ZesuSsz.Contracts.ParentHeaderSuccessWalk.

Definition parentHeaderWalkAt (args : ParentHeaderArgs) (k : nat) (p l : bv 64) (acc : list Z) : Prop :=
  candidateWalkState (parentHeaderInputBytes args) k
    (bv_unsigned p - bv_unsigned (parentHeaderInputPointer args))%Z (bv_unsigned l) acc /\
  bv_unsigned l <> 0%Z.

Definition parentHeaderWalkStart (args : ParentHeaderArgs) (after : list byte) : Prop :=
  parentHeaderWalkAt args 0 (listWord64At0 after) (listWord64At8 after) [].

Definition parentHeaderWalkSkipped (args : ParentHeaderArgs) (k : nat) (p l : bv 64) (after : list byte)
    (acc : list Z) : Prop :=
  parentHeaderWalkAt args k (bv_add p (listWord64At24 after)) (bv_sub l (listWord64At24 after)) acc.

(* The outer item: decodeItem succeeded on the whole input with a non-empty
   list (the guards of blocks 0x0040, 0x0054 and 0x0060). *)
Lemma parentHeaderWalkStartOf args before after :
  headerFits (parentHeaderInputBytes args) ->
  C1BResult (bv_unsigned (parentHeaderInputPointer args)) (parentHeaderInputBytes args) before after ->
  bv_unsigned (bv_concat 16 (List.nth 33 after (BV 8 0)) (List.nth 32 after (BV 8 0))) = 0 ->
  bv_unsigned (bv_and (bv_zero_extend 64 (List.nth 16 after (BV 8 0))) (BV 64 1)) <> 0 ->
  bv_unsigned (listWord64At8 after) <> 0 ->
  parentHeaderWalkStart args after.
Proof.
  intros Hfits Hres Hok Hlist Hlen. split; [|exact Hlen].
  exact (candidateWalkStart _ _ _ _ Hfits Hres Hok Hlist Hlen).
Qed.

(* A skipped field: its call succeeded (status half-word 0) and the code
   found something left after it ([l <> consumed]). *)
Lemma parentHeaderWalkSkipOf args k pc kind (p l : bv 64) acc before after :
  nth_error parentHeaderFieldSchedule k = Some (pc, kind) ->
  parentHeaderFieldIsInteger kind = false ->
  parentHeaderWalkAt args k p l acc ->
  C1BResult (bv_unsigned p)
    (take (Z.to_nat (bv_unsigned l))
      (drop (Z.to_nat (bv_unsigned p - bv_unsigned (parentHeaderInputPointer args))) (parentHeaderInputBytes args)))
    before after ->
  bv_unsigned (bv_concat 16 (List.nth 33 after (BV 8 0)) (List.nth 32 after (BV 8 0))) = 0 ->
  l <> listWord64At24 after ->
  parentHeaderWalkSkipped args (S k) p l after acc.
Proof.
  intros Hk Hint [Hs Hl] Hres Hok Hleft. split.
  - exact (candidateWalkSkipMachine _ _ _ _ _ _ _ _ _ _ Hk Hint Hs Hl Hres Hok).
  - apply walkRemainingNonzero. intros E. apply Hleft, bv_eq. exact E.
Qed.

(* Fields 9 to 11 (inline integers): the code does not test "something
   left" before their calls (0x023c, 0x02e4, 0x0348), so their return sites
   state the walk without it: [parentHeaderWalkState]; the window after a
   call on [p, p + l) with outcome [after] is [parentHeaderWalkSkippedState]. *)
Definition parentHeaderWalkState (args : ParentHeaderArgs) (k : nat) (p l : bv 64) (acc : list Z) : Prop :=
  candidateWalkState (parentHeaderInputBytes args) k
    (bv_unsigned p - bv_unsigned (parentHeaderInputPointer args))%Z (bv_unsigned l) acc.

Definition parentHeaderWalkSkippedState (args : ParentHeaderArgs) (k : nat) (p l : bv 64)
    (after : list byte) (acc : list Z) : Prop :=
  parentHeaderWalkState args k (bv_add p (listWord64At24 after)) (bv_sub l (listWord64At24 after)) acc.

(* A skipped field (8) whose call succeeded; no "something left" test follows. *)
Lemma parentHeaderWalkSkipStateOf args k pc kind (p l : bv 64) acc before after :
  nth_error parentHeaderFieldSchedule k = Some (pc, kind) ->
  parentHeaderFieldIsInteger kind = false ->
  parentHeaderWalkAt args k p l acc ->
  C1BResult (bv_unsigned p)
    (take (Z.to_nat (bv_unsigned l))
      (drop (Z.to_nat (bv_unsigned p - bv_unsigned (parentHeaderInputPointer args))) (parentHeaderInputBytes args)))
    before after ->
  bv_unsigned (bv_concat 16 (List.nth 33 after (BV 8 0)) (List.nth 32 after (BV 8 0))) = 0 ->
  parentHeaderWalkSkippedState args (S k) p l after acc.
Proof.
  intros Hk Hint [Hs Hl] Hres Hok.
  exact (candidateWalkSkipMachine _ _ _ _ _ _ _ _ _ _ Hk Hint Hs Hl Hres Hok).
Qed.

(* An inline integer field: its call succeeded with a string (list bit 0)
   of at most 8 payload bytes, and the value register [x] holds the loop's
   fold of the payload. The window was not empty: decodeItem fails on an
   empty input. [acc'] is the value list the return site names. *)
Lemma parentHeaderWalkIntegerOf args k pc kind (p l x : bv 64) acc acc' before after :
  nth_error parentHeaderFieldSchedule k = Some (pc, kind) ->
  parentHeaderFieldIsInteger kind = true ->
  parentHeaderWalkState args k p l acc ->
  C1BResult (bv_unsigned p)
    (take (Z.to_nat (bv_unsigned l))
      (drop (Z.to_nat (bv_unsigned p - bv_unsigned (parentHeaderInputPointer args))) (parentHeaderInputBytes args)))
    before after ->
  bv_unsigned (bv_concat 16 (List.nth 33 after (BV 8 0)) (List.nth 32 after (BV 8 0))) = 0 ->
  bv_unsigned (bv_and (bv_zero_extend 64 (List.nth 16 after (BV 8 0))) (BV 64 1)) = 0 ->
  ~ (bv_signed (BV 128 8) < bv_signed (bv_zero_extend 128 (listWord64At8 after))) ->
  bv_unsigned x = zesu_byte_window_fold (parentHeaderInputBytes args)
    (Z.to_nat (bv_unsigned (listWord64At0 after) - bv_unsigned (parentHeaderInputPointer args)))
    (Z.to_nat (bv_unsigned (listWord64At8 after))) ->
  acc' = acc ++ [bv_unsigned x] ->
  parentHeaderWalkSkippedState args (S k) p l after acc'.
Proof.
  intros Hk Hint Hs Hres Hok Hstr H8 Hx ->.
  rewrite zesu_signed_zero_extend_64_128 in H8.
  assert (E8 : bv_signed (BV 128 8) = 8) by reflexivity. rewrite E8 in H8.
  destruct (c1bSuccess _ _ _ _ Hres Hok) as (isList & h & pl & Hcand & Hp & _ & _ & Hptr).
  assert (Hl0 : bv_unsigned l <> 0).
  { intros E. rewrite E in Hcand. cbn in Hcand. discriminate Hcand. }
  pose proof Hs as (Hc & _).
  unfold parentHeaderWalkSkippedState, parentHeaderWalkState.
  eapply walkStateMachine; [exact Hs|exact Hres|].
  rewrite Hx, (integerValueFold _ _ _ _ _ _ isList h pl Hc Hres Hcand Hp ltac:(lia) Hptr).
  exact (candidateWalkIntegerStep _ _ _ _ _ _ _ _ _ _ _ Hk Hint Hs Hl0 Hres Hok Hstr ltac:(lia) eq_refl).
Qed.

(* The last inline integer field (11), then "something left" (0x03b0). *)
Lemma parentHeaderWalkIntegerLeftOf args k pc kind (p l x : bv 64) acc acc' before after :
  nth_error parentHeaderFieldSchedule k = Some (pc, kind) ->
  parentHeaderFieldIsInteger kind = true ->
  parentHeaderWalkState args k p l acc ->
  C1BResult (bv_unsigned p)
    (take (Z.to_nat (bv_unsigned l))
      (drop (Z.to_nat (bv_unsigned p - bv_unsigned (parentHeaderInputPointer args))) (parentHeaderInputBytes args)))
    before after ->
  bv_unsigned (bv_concat 16 (List.nth 33 after (BV 8 0)) (List.nth 32 after (BV 8 0))) = 0 ->
  bv_unsigned (bv_and (bv_zero_extend 64 (List.nth 16 after (BV 8 0))) (BV 64 1)) = 0 ->
  ~ (bv_signed (BV 128 8) < bv_signed (bv_zero_extend 128 (listWord64At8 after))) ->
  bv_unsigned x = zesu_byte_window_fold (parentHeaderInputBytes args)
    (Z.to_nat (bv_unsigned (listWord64At0 after) - bv_unsigned (parentHeaderInputPointer args)))
    (Z.to_nat (bv_unsigned (listWord64At8 after))) ->
  l <> listWord64At24 after ->
  acc' = acc ++ [bv_unsigned x] ->
  parentHeaderWalkSkipped args (S k) p l after acc'.
Proof.
  intros Hk Hint Hs Hres Hok Hstr H8 Hx Hleft Hacc. split.
  - exact (parentHeaderWalkIntegerOf _ _ _ _ _ _ _ _ _ _ _ Hk Hint Hs Hres Hok Hstr H8 Hx Hacc).
  - apply walkRemainingNonzero. intros E. apply Hleft, bv_eq. exact E.
Qed.

(* The success join 0x03bc: nothing is left before an optional field (12, 13
   or 14). The candidate accepts with the values the join stores. *)
Lemma parentHeaderRemainingNone (l w : bv 64) : l = w -> bv_unsigned (bv_sub l w) = 0.
Proof. intros ->. rewrite bv_sub_unsigned, Z.sub_diag. reflexivity. Qed.

(* After the last inline integer field (11). *)
Lemma parentHeaderSuccessAfterInteger args k pc kind pc' kind' (p l x : bv 64) acc acc' before after :
  nth_error parentHeaderFieldSchedule k = Some (pc, kind) ->
  parentHeaderFieldIsInteger kind = true ->
  nth_error parentHeaderFieldSchedule (S k) = Some (pc', kind') ->
  parentHeaderFieldIsRequired kind' = false ->
  parentHeaderWalkState args k p l acc ->
  C1BResult (bv_unsigned p)
    (take (Z.to_nat (bv_unsigned l))
      (drop (Z.to_nat (bv_unsigned p - bv_unsigned (parentHeaderInputPointer args))) (parentHeaderInputBytes args)))
    before after ->
  bv_unsigned (bv_concat 16 (List.nth 33 after (BV 8 0)) (List.nth 32 after (BV 8 0))) = 0 ->
  bv_unsigned (bv_and (bv_zero_extend 64 (List.nth 16 after (BV 8 0))) (BV 64 1)) = 0 ->
  ~ (bv_signed (BV 128 8) < bv_signed (bv_zero_extend 128 (listWord64At8 after))) ->
  bv_unsigned x = zesu_byte_window_fold (parentHeaderInputBytes args)
    (Z.to_nat (bv_unsigned (listWord64At0 after) - bv_unsigned (parentHeaderInputPointer args)))
    (Z.to_nat (bv_unsigned (listWord64At8 after))) ->
  l = listWord64At24 after ->
  acc' = acc ++ [bv_unsigned x] ->
  candidateParentHeader (parentHeaderInputBytes args) = candidateHeaderSuccess (candidateHeaderOfValues acc').
Proof.
  intros Hk Hint Hk' Hopt Hs Hres Hok Hstr H8 Hx Hnone Hacc.
  pose proof (parentHeaderWalkIntegerOf _ _ _ _ _ _ _ _ _ _ _ Hk Hint Hs Hres Hok Hstr H8 Hx Hacc) as Hs'.
  unfold parentHeaderWalkSkippedState, parentHeaderWalkState in Hs'.
  rewrite (parentHeaderRemainingNone _ _ Hnone) in Hs'.
  exact (candidateWalkAbsent _ _ _ _ _ _ Hk' Hopt Hs').
Qed.

(* After an optional skipped field (12 or 13). *)
Lemma parentHeaderSuccessAfterSkip args k pc kind pc' kind' (p l : bv 64) acc before after :
  nth_error parentHeaderFieldSchedule k = Some (pc, kind) ->
  parentHeaderFieldIsInteger kind = false ->
  nth_error parentHeaderFieldSchedule (S k) = Some (pc', kind') ->
  parentHeaderFieldIsRequired kind' = false ->
  parentHeaderWalkAt args k p l acc ->
  C1BResult (bv_unsigned p)
    (take (Z.to_nat (bv_unsigned l))
      (drop (Z.to_nat (bv_unsigned p - bv_unsigned (parentHeaderInputPointer args))) (parentHeaderInputBytes args)))
    before after ->
  bv_unsigned (bv_concat 16 (List.nth 33 after (BV 8 0)) (List.nth 32 after (BV 8 0))) = 0 ->
  l = listWord64At24 after ->
  candidateParentHeader (parentHeaderInputBytes args) = candidateHeaderSuccess (candidateHeaderOfValues acc).
Proof.
  intros Hk Hint Hk' Hopt Hs Hres Hok Hnone.
  pose proof (parentHeaderWalkSkipStateOf _ _ _ _ _ _ _ _ _ Hk Hint Hs Hres Hok) as Hs'.
  unfold parentHeaderWalkSkippedState, parentHeaderWalkState in Hs'.
  rewrite (parentHeaderRemainingNone _ _ Hnone) in Hs'.
  exact (candidateWalkAbsent _ _ _ _ _ _ Hk' Hopt Hs').
Qed.
