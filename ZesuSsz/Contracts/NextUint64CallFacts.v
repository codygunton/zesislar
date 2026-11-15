From Coq Require Import List ZArith Lia.
From stdpp Require Import base list numbers bitvector.definitions.
Require Import EvmSailRlp.evm_rlp_types.
Require Import ZesuSsz.Contracts.RlpDecodeItem.
Require Import ZesuSsz.Contracts.ParentHeader.
Require Import ZesuSsz.Contracts.ParentHeaderRootFacts.
Require Import ZesuSsz.Contracts.NextUint64BlockEntries.
Require Import ZesuSsz.Contracts.DecodeItemPayloadBounds.

Import ListNotations.
Open Scope Z_scope.

(* Proofs of nextUint64's interface lemmas, over the real definitions
   (the pattern of DecodeItemCallFacts.v). ZesuSsz/Interfaces/NextUint64.v
   states each over the sealed domain and result. *)

Lemma bigEndianFoldNonneg (bytes : list byte) acc :
  0 <= acc -> 0 <= List.fold_left (fun acc b => 256 * acc + bv_unsigned b) bytes acc.
Proof.
  revert acc. induction bytes as [|b bytes IH]; intros acc Hacc; cbn; [lia|].
  apply IH. apply Z.add_nonneg_nonneg; [lia|exact (proj1 (bv_unsigned_in_range _ b))].
Qed.

Lemma candidateDecodeItemPayloadNonneg input isList headerLength payloadLength :
  candidateDecodeItem input = candidateSuccess isList headerLength payloadLength ->
  0 <= payloadLength.
Proof.
  destruct input as [|prefix rest]; [discriminate|].
  pose proof (bv_unsigned_in_range _ prefix) as Hp. unfold bv_modulus in Hp.
  change (2 ^ Z.of_N (MachineWord.MachineWord.Z_idx 8)) with 256 in Hp.
  unfold candidateDecodeItem, checkedPayload, bigEndian. cbn zeta. intros H.
  repeat (case_match; simplify_eq);
    rewrite ?andb_true_iff, ?Z.leb_le, ?Z.leb_gt, ?Z.eqb_eq, ?Z.eqb_neq in *.
  all: change (MachineWord.MachineWord.Z_idx 8) with 8%N in *.
  all: first [lia | apply bigEndianFoldNonneg; lia].
Qed.

(* nextUint64RootResult in the caller's terms: a 16-byte result, an input
   address that fits, and a rest slice inside the input (unchanged on an
   error, advanced by the consumed item of at most 17 bytes on success). *)
Lemma nextUint64RootResultCallerFacts call result :
  nextUint64RootResult call result ->
  (List.length (nextResultBytes result) = 16)%nat /\
  0 <= nextInputPointer call /\
  nextInputPointer call + Z.of_nat (length (nextInputBytes call)) < 18446744073709551616 /\
  nextInputPointer call <= nextRestPointer result /\
  nextRestPointer result + nextRestLength result =
    nextInputPointer call + Z.of_nat (length (nextInputBytes call)) /\
  0 <= nextRestLength result <= Z.of_nat (length (nextInputBytes call)).
Proof.
  unfold nextUint64RootResult, inputAddressFits. intros ((Hlow & Hhigh) & Hresult).
  change (2 ^ 64) with 18446744073709551616 in Hhigh.
  destruct (candidateDecodeItem (nextInputBytes call)) as [|isList h p] eqn:Hc.
  - destruct Hresult as ((Hlen & _) & Hptr & Hcount). lia.
  - destruct (isList || (8 <? p)) eqn:Hkind.
    + destruct Hresult as ((Hlen & _) & Hptr & Hcount). lia.
    + destruct Hresult as ((Hlen & _) & Hptr & Hcount).
      destruct (candidateDecodeItemSuccessBounds _ _ _ _ Hc) as (Hh & Hfit & _).
      pose proof (candidateDecodeItemPayloadNonneg _ _ _ _ Hc) as Hp.
      apply orb_false_iff in Hkind as [_ Hsmall]. apply Z.ltb_ge in Hsmall.
      change (2 ^ 64) with 18446744073709551616 in Hfit.
      rewrite Z.mod_small in Hfit by lia. lia.
Qed.

(* ---- The interface lemmas (proof sources of proved_functions.json). ---- *)

Lemma nextUint64ResultLength call result :
  nextUint64RootResult call result -> (List.length (nextResultBytes result) = 16)%nat.
Proof. intros H. exact (proj1 (nextUint64RootResultCallerFacts _ _ H)). Qed.

(* The rest slice the caller stores back lies inside the input. Stated on the
   call record, so the facts name the caller's terms. *)
Lemma nextUint64ResultRest
    inputPointer input slice resultPointer stack returnAddress s0 s1 s2 s3 s4 result :
  nextUint64RootResult
    {| nextInputPointer := inputPointer; nextInputBytes := input;
       nextSlicePointer := slice; nextResultPointer := resultPointer;
       nextStackPointer := stack; nextReturnAddress := returnAddress;
       nextSavedS0 := s0; nextSavedS1 := s1; nextSavedS2 := s2;
       nextSavedS3 := s3; nextSavedS4 := s4 |} result ->
  0 <= inputPointer /\
  inputPointer + Z.of_nat (length input) < 18446744073709551616 /\
  inputPointer <= nextRestPointer result /\
  nextRestPointer result + nextRestLength result = inputPointer + Z.of_nat (length input) /\
  0 <= nextRestLength result <= Z.of_nat (length input).
Proof. intros H. exact (proj2 (nextUint64RootResultCallerFacts _ _ H)). Qed.

(* The call site establishes the sealed domain from nextUint64's stated
   precondition; a caller's exit composition reads the result back. Inside
   the sealed implementation both are the identity. *)
Lemma nextUint64DomainIntro params :
  nextUint64BoundaryDomain params -> nextUint64BoundaryDomain params.
Proof. exact id. Qed.

Lemma nextUint64ResultLink call result :
  nextUint64RootResult call result -> nextUint64RootResult call result.
Proof. exact id. Qed.
