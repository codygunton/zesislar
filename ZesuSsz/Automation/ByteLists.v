(* Byte-list resources: a list of (data pointer, size) items, 16 bytes
   per item, each item owning the bytes its pointer names. Moved from
   the writeSuccess proof tree so the retained hooks in
   `Automation/ByteListResources.v` do not import an endpoint proof. *)
Require Import ZesuSsz.Automation.AllLegacy.
From Coq Require Import Lists.List ZArith.ZArith.
Require Import isla.riscv64.riscv64.

Import ListNotations.


Record ByteListItem : Type := {
  byteListData : bv 64;
  byteListSize : bv 64;
  byteListBytes : list (bv 8)
}.

Fixpoint byteListItemResources `{!islaG Sigma} (address : Z)
    (items : list ByteListItem) : iProp Sigma :=
  match items with
  | [] => True
  | item :: rest =>
      (address ↦ₘ byteListData item ∗
       (address + 8) ↦ₘ byteListSize item ∗
       bv_unsigned (byteListData item) ↦ₘ∗ byteListBytes item ∗
       ⌜bv_unsigned (byteListSize item) = length (byteListBytes item)⌝ ∗
       byteListItemResources (address + 16) rest)%I
  end.

Global Instance : LithiumUnfold (@byteListItemResources) := I.

Lemma byteListItemResources_app `{!islaG Sigma} (address : Z)
    (left right : list ByteListItem) :
  byteListItemResources address (left ++ right) -∗
  byteListItemResources address left ∗
  byteListItemResources (address + 16 * Z.of_nat (length left)) right.
Proof.
  iInduction left as [|item left] "IH" forall (address); simpl.
  - iIntros "Hright". iSplit; first done.
    replace (address + 16 * 0%nat)%Z with address by lia.
    iExact "Hright".
  - iIntros "Hresources".
    iDestruct "Hresources" as "(Hdata & Hsize & Hbytes & %Hlength & Hrest)".
    iDestruct ("IH" $! (address + 16)%Z with "Hrest") as "[Hleft Hright]".
    iSplitL "Hdata Hsize Hbytes Hleft".
    { iFrame. done. }
    replace (address + 16 + 16 * Z.of_nat (length left))%Z with
      (address + 16 * Z.of_nat (length (item :: left)))%Z by (simpl; lia).
    iExact "Hright".
Qed.

Lemma byteListItemResources_app_combine `{!islaG Sigma} (address : Z)
    (left right : list ByteListItem) :
  byteListItemResources address left -∗
  byteListItemResources (address + 16 * Z.of_nat (length left)) right -∗
  byteListItemResources address (left ++ right).
Proof.
  iInduction left as [|item left] "IH" forall (address); simpl.
  - iIntros "_ Hright".
    have Hzero : (address + 16 * 0%nat)%Z = address by lia.
    iEval (rewrite Hzero) in "Hright".
    iExact "Hright".
  - iIntros "Hleft Hright".
    iDestruct "Hleft" as "(Hdata & Hsize & Hbytes & %Hlength & Hleft)".
    iFrame.
    iSplit; first done.
    have Haddress :
      (address + 16 * Z.of_nat (length (item :: left)))%Z =
      (address + 16 + 16 * Z.of_nat (length left))%Z by (simpl; lia).
    iEval (rewrite Haddress) in "Hright".
    iPoseProof ("IH" $! (address + 16)%Z with "Hleft Hright") as "Hcombined".
    iExact "Hcombined".
Qed.

Definition byteListProcessedResources `{!islaG Sigma} (address : Z)
    (items : list ByteListItem) : iProp Sigma :=
  byteListItemResources address items.

Lemma byteListProcessedResources_combine `{!islaG Sigma} (address : Z)
    (left right : list ByteListItem) :
  byteListProcessedResources address left -∗
  byteListItemResources (address + 16 * Z.of_nat (length left)) right -∗
  byteListItemResources address (left ++ right).
Proof.
  rewrite /byteListProcessedResources.
  apply byteListItemResources_app_combine.
Qed.

Lemma byteListProcessedResources_snoc `{!islaG Sigma} (address : Z)
    (items : list ByteListItem) (item : ByteListItem) :
  byteListProcessedResources address items -∗
  byteListItemResources (address + 16 * Z.of_nat (length items)) [item] -∗
  byteListProcessedResources address (items ++ [item]).
Proof.
  rewrite /byteListProcessedResources.
  apply byteListItemResources_app_combine.
Qed.

Lemma byteListProcessedResources_nil `{!islaG Sigma} (address : Z) :
  ⊢ byteListProcessedResources address [].
Proof. move => *. zesu_block. Qed.

Global Opaque byteListProcessedResources.

Definition byteListEndPointer (pointer : bv 64)
    (items : list ByteListItem) : bv 64 :=
  (pointer + Z_to_bv 64 (8 + 16 * Z.of_nat (length items)))%bv.
