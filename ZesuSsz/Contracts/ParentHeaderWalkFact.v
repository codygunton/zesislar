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
