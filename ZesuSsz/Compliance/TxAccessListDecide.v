(* Decision instances for the premises of txAccessList's residual goals, so that the
   real-state screen (tools/oblig/normalise.py, tools/oblig/falsify.py) evaluates them on
   snapshot values. Screening only: no block proof imports this module; the screen loads it
   through the binder map's `imports` (tools/oblig/exec/binders/txAccessList.json).
   decodeItemCallDomain and decodeItemCallMeaning are Parameters of the sealed interface
   (ZesuSsz/Interfaces/DecodeItem.v) and get no instance here. *)
From Coq Require Import List ZArith Znumtheory.
From stdpp Require Import base decidable list numbers bitvector.definitions.
Require Import EvmSailRlp.evm_rlp_types.
Require Import ZesuSsz.Automation2.Hist.
Require Import ZesuSsz.Automation2.ContextCollection.
Require Import ZesuSsz.Automation2.Hooks.
Require Import ZesuSsz.Automation2.RegisterArrayCursor.
Require Import ZesuSsz.Contracts.NamedEquation.
Require Import ZesuSsz.Contracts.RlpDecodeItem.
Require Import ZesuSsz.Contracts.Candidates.AccessListCandidate.
Require Import ZesuSsz.Contracts.TxAccessListContract.
Require Import ZesuSsz.Contracts.TxAccessListMeaning.
Require Import ZesuSsz.Contracts.TxAccessListBlockEntries.
Require Import ZesuSsz.Contracts.TxAccessListLoopFacts.
Local Open Scope Z_scope.

(* Markers of the automation: inhabited by their single constructor. *)
Global Instance zesu_context_finish_attempted_dec {A : Type} (t : A) :
  Decision (zesu_context_finish_attempted t) := left (zesu_context_finish_token t).
Global Instance zesu_canonical_fact_views_attempted_dec {A : Type} (t : A) :
  Decision (zesu_canonical_fact_views_attempted t) := left (zesu_canonical_fact_views_token t).
Global Instance zesu_register_cursor_attempted_dec {A : Type} (t : A) :
  Decision (zesu_register_cursor_attempted t) := left (zesu_register_cursor_token t).

(* A history fact and a named equation decide as the fact they wrap. *)
Global Instance zesu_hist_dec (P : Prop) `{!Decision P} : Decision (zesu_hist P).
Proof. rewrite zesu_hist_eq. unfold zesu_hist_def. apply _. Defined.
Global Instance zesu_named_eq_dec {A : Type} `{!EqDecision A} (n v : A) :
  Decision (zesu_named_eq n v).
Proof. destruct (decide (n = v)); [left | right]; rewrite zesu_named_eq_iff; done. Defined.

Global Instance zesu_Z_divide_dec (a b : Z) : Decision (Z.divide a b) := Zdivide_dec a b.

Global Instance separateRanges_dec (a la b lb : Z) : Decision (separateRanges a la b lb).
Proof. unfold separateRanges. apply _. Defined.

Global Instance headerFits_dec (bytes : list byte) : Decision (headerFits bytes).
Proof. unfold headerFits. destruct bytes; apply _. Defined.

Global Instance accessListHeadersFit_dec (input : list byte) : Decision (accessListHeadersFit input).
Proof. unfold accessListHeadersFit. apply _. Defined.

Global Instance txAccessListDomain_dec (input : list byte) : Decision (txAccessListDomain input).
Proof. unfold txAccessListDomain. destruct (candidateDecodeItem input); apply _. Defined.

Global Instance txAccessListArgsWellFormed_dec (args : TxAccessListArgs) :
  Decision (txAccessListArgsWellFormed args).
Proof. unfold txAccessListArgsWellFormed. apply _. Defined.

Global Instance txAccessListBlockArgsWellFormed_dec (args : TxAccessListArgs) :
  Decision (txAccessListBlockArgsWellFormed args).
Proof. unfold txAccessListBlockArgsWellFormed. apply _. Defined.

Global Instance txAccessListBlockDomainAt_dec (returnAddress : Z) (args : TxAccessListArgs) :
  Decision (txAccessListBlockDomainAt returnAddress args).
Proof. unfold txAccessListBlockDomainAt. apply _. Defined.

Global Instance txAccessListKeysWalked_dec (keysPayload : list byte) (offset : Z)
    (doneKeys : list (list byte)) : Decision (txAccessListKeysWalked keysPayload offset doneKeys).
Proof. unfold txAccessListKeysWalked. apply _. Defined.

Global Instance AccessListEntryValue_eq_dec : EqDecision AccessListEntryValue.
Proof.
  intros [a k] [b l]. destruct (decide (a = b)) as [->|Ha]; [destruct (decide (k = l)) as [->|Hk]|].
  - left. reflexivity.
  - right. congruence.
  - right. congruence.
Defined.

(* The walk's header and payload lengths are the candidate's: decide by its outcome. *)
Global Instance txAccessListOuterWalked_dec
    (input : list byte) (offset : Z) (done : list AccessListEntryValue) :
  Decision (txAccessListOuterWalked input offset done).
Proof.
  unfold txAccessListOuterWalked.
  destruct (candidateDecodeItem input) as [|isList h p] eqn:Hc.
  - right. intros (h' & p' & Hs & _). congruence.
  - destruct (decide (isList = true /\ h <= offset <= h + p /\
      snd (accessListEntriesWalk (List.length (itemPayload input h p)) (itemPayload input h p)) =
      option_map (app done) (snd (accessListEntriesWalk
        (List.length (skipn (Z.to_nat (offset - h)) (itemPayload input h p)))
        (skipn (Z.to_nat (offset - h)) (itemPayload input h p)))))) as [Hy|Hn].
    + left. destruct Hy as (-> & Hr & Hw). exists h, p. auto.
    + right. intros (h' & p' & Hs & Hr & Hw).
      injection Hs as Hl Hh Hp. subst. apply Hn. auto.
Defined.
