Require Import ZesuSsz.Automation.All.
From Coq Require Import List ZArith Lia.
From stdpp Require Import bitvector.definitions.
Require Import EvmSailRlp.evm_rlp_types.
Require Import ZesuSsz.Compliance.ByteFold.
Require Import ZesuSsz.Contracts.RlpDecodeItem.
Require Import ZesuSsz.Contracts.RlpDecodeItemContract.
Require Import ZesuSsz.Contracts.RlpDecodeItemByteFold.
Require Import ZesuSsz.Contracts.RlpDecodeItemByteFoldSites.

Import ListNotations.
Open Scope Z_scope.

Lemma decodeItem_firstn_snoc (bytes : list byte) (index : nat) (next : byte) :
  nth_error bytes index = Some next ->
  firstn (S index) bytes = firstn index bytes ++ [next].
Proof.
  revert index.
  induction bytes as [|head tail IH]; intros [|index] Hnext;
    simpl in *; try discriminate.
  - inversion Hnext. reflexivity.
  - f_equal. apply IH. exact Hnext.
Qed.

Lemma decodeItem_fold_entry (args : DecodeItemArgs) n payloadStart lengthBytes :
  decodeItemByteFoldFacts args n 0 payloadStart lengthBytes ->
  0 < n /\ bigEndian (firstn 0 lengthBytes) = 0 /\
  payloadStart + 0 = payloadStart.
Proof.
  unfold decodeItemByteFoldFacts.
  intros [Hn _]. unfold bigEndian. simpl. lia.
Qed.

Lemma decodeItem_fold_preservation (args : DecodeItemArgs)
    n i payloadStart lengthBytes next :
  decodeItemByteFoldFacts args n i payloadStart lengthBytes ->
  i < n -> nth_error lengthBytes (Z.to_nat i) = Some next ->
  decodeItemByteFoldFacts args n (i + 1) payloadStart lengthBytes /\
  bigEndian (firstn (Z.to_nat (i + 1)) lengthBytes) =
    256 * bigEndian (firstn (Z.to_nat i) lengthBytes) + bv_unsigned next.
Proof.
  intros Hfacts Hmore Hnext.
  split.
  - unfold decodeItemByteFoldFacts in *.
    destruct Hfacts as [Hn [Hi [Hstart [Hbytes [Hlength Hbound]]]]].
    repeat split; try lia; assumption.
  - unfold decodeItemByteFoldFacts in Hfacts.
    destruct Hfacts as [_ [Hi _]].
    rewrite Z2Nat.inj_succ by lia.
    rewrite (decodeItem_firstn_snoc lengthBytes (Z.to_nat i) next Hnext).
    apply zesu_bigEndian_snoc.
Qed.

Lemma decodeItem_fold_exit (args : DecodeItemArgs)
    n payloadStart lengthBytes :
  decodeItemByteFoldFacts args n n payloadStart lengthBytes ->
  bigEndian (firstn (Z.to_nat n) lengthBytes) = bigEndian lengthBytes /\
  payloadStart + n = decodeItemInputPointer args + 1 + n.
Proof.
  unfold decodeItemByteFoldFacts.
  intros [_ [_ [Hstart [_ [Hlength _]]]]].
  split; [rewrite <- Hlength; rewrite Nat2Z.id; rewrite firstn_all; reflexivity|].
  lia.
Qed.

(* Both headers use the same byte fold. Their distinct PCs remain explicit. *)
Lemma decodeItem_string_fold_pc :
  decodeItemByteFoldHeader false = decodeItemStringFoldPC.
Proof. reflexivity. Qed.

Lemma decodeItem_list_fold_pc :
  decodeItemByteFoldHeader true = decodeItemListFoldPC.
Proof. reflexivity. Qed.

Print Assumptions decodeItem_fold_entry.
Print Assumptions decodeItem_fold_preservation.
Print Assumptions decodeItem_fold_exit.
