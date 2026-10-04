From Coq Require Import List String ZArith.
Require Import EvmSailRlp.evm_rlp_types.
Require Import ZesuSsz.Contracts.RlpDecodeItem.
Require Import ZesuSsz.Contracts.ParentHeader.
Require Import ZesuSsz.Contracts.ParentHeaderRootFacts.
Require Import ZesuSsz.Contracts.ParentHeaderLevel1.

Import ListNotations.
Open Scope Z_scope.

(* The selected inventory's canonical JSON, without artifact_identity, has
   SHA256 ac8d71ba0c1fef4597c74648c8d6d0dbf8ac9783707560c659a4049a208016c2.
   Its decoded CFG gives these 20 call PCs and the shown targets. The three
   optional Uint64Field entries call nextUint64; all other entries call
   decodeItem directly, including three inlined required integers. *)
Definition parentHeaderInventorySha256 : string :=
  "ac8d71ba0c1fef4597c74648c8d6d0dbf8ac9783707560c659a4049a208016c2"%string.

Inductive ParentHeaderFieldKind :=
| RequiredSkip | RequiredUint64 | OptionalSkip | OptionalUint64.

Definition parentHeaderFieldSchedule : list (Z * ParentHeaderFieldKind) :=
  [(0x800d5d34, RequiredSkip); (0x800d5dbc, RequiredSkip);
   (0x800d5de8, RequiredSkip); (0x800d5e14, RequiredSkip);
   (0x800d5e40, RequiredSkip); (0x800d5e6c, RequiredSkip);
   (0x800d5e98, RequiredSkip); (0x800d5ec4, RequiredSkip);
   (0x800d5ef0, RequiredSkip);
   (0x800d5f18, RequiredUint64); (0x800d5fb4, RequiredUint64);
   (0x800d601c, RequiredUint64);
   (0x800d60b4, OptionalSkip); (0x800d60ec, OptionalSkip);
   (0x800d6118, OptionalSkip);
   (0x800d615c, OptionalUint64); (0x800d6198, OptionalSkip);
   (0x800d621c, OptionalUint64); (0x800d6250, OptionalUint64)].

Definition positiveItemWithin (bytes : list byte)
    (headerLength payloadLength : Z) : bool :=
  (0 <? headerLength + payloadLength) &&
  (headerLength + payloadLength <=? Z.of_nat (List.length bytes)).

Fixpoint reachedFieldSlices (schedule : list (Z * ParentHeaderFieldKind))
    (remaining : list byte) : option (list (Z * list byte)) :=
  match schedule with
  | [] => Some []
  | (pc, kind) :: later =>
      match remaining with
      | [] =>
          match kind with
          | RequiredUint64 => Some [(pc, [])]
          | _ => Some []
          end
      | _ =>
          match candidateDecodeItem remaining with
          | candidateError => Some [(pc, remaining)]
          | candidateSuccess isList headerLength payloadLength =>
              if positiveItemWithin remaining headerLength payloadLength then
                if match kind with
                   | RequiredSkip | OptionalSkip => false
                   | RequiredUint64 | OptionalUint64 =>
                       isList || (8 <? payloadLength)
                   end then Some [(pc, remaining)]
                else
                  option_map (cons (pc, remaining))
                    (reachedFieldSlices later
                      (skipn (Z.to_nat (headerLength + payloadLength)) remaining))
              else Some [(pc, remaining)]
          end
      end
  end.

Definition fieldSlices (input : list byte) : option (list (Z * list byte)) :=
  match candidateDecodeItem input with
  | candidateError => Some [(0x800d5cf4, input)]
  | candidateSuccess isList headerLength payloadLength =>
      if positiveItemWithin input headerLength payloadLength then
        if isList then
          option_map (cons (0x800d5cf4, input))
            (reachedFieldSlices parentHeaderFieldSchedule
              (firstn (Z.to_nat payloadLength)
                (skipn (Z.to_nat headerLength) input)))
        else Some [(0x800d5cf4, input)]
      else None
  end.

Definition allContiguousHeadersFit (input : list byte) : Prop :=
  headerFits input /\
  exists slices, fieldSlices input = Some slices /\
    List.Forall (fun call => headerFits (snd call)) slices.

Definition candidateCallInputAt (input : list byte)
    (pc : Z) (remaining : list byte) : Prop :=
  exists slices, fieldSlices input = Some slices /\
    List.In (pc, remaining) slices.

Lemma candidateDomainImpliesNestedC1A input :
  allContiguousHeadersFit input ->
  nestedC1AObligation (candidateCallInputAt input).
Proof.
  intros [_ [slices [Hwalk Hfits]]] pc remaining _ [other [Hother Hin]].
  rewrite Hwalk in Hother. inversion Hother; subst other.
  rewrite List.Forall_forall in Hfits.
  exact (Hfits _ Hin).
Qed.

(* Machine proofs must establish this relation for actual reached calls.
   The pure candidate walk does not establish machine-call correspondence. *)
Definition reachedCallCorrespondence (input : list byte)
    (callInputAt : Z -> list byte -> Prop) : Prop :=
  forall pc remaining,
    List.In pc
      (parentHeaderDecodeItemCallSites ++ parentHeaderNextUint64CallSites) ->
    callInputAt pc remaining -> candidateCallInputAt input pc remaining.

Lemma candidateDomainWithCorrespondence input callInputAt :
  allContiguousHeadersFit input ->
  reachedCallCorrespondence input callInputAt ->
  nestedC1AObligation callInputAt.
Proof.
  intros Hfit Hmatch pc remaining Hsite Hcall.
  apply (candidateDomainImpliesNestedC1A input Hfit pc remaining Hsite).
  exact (Hmatch pc remaining Hsite Hcall).
Qed.

(* This pure walk identifies a possible nested length wrap. The machine
   proof must connect each reached call to the walked slice. *)
Definition nestedWrapOccurs (input : list byte) : Prop :=
  exists pc remaining isList headerLength payloadLength,
    pc <> 0x800d5cf4 /\
    List.In pc
      (parentHeaderDecodeItemCallSites ++ parentHeaderNextUint64CallSites) /\
    candidateCallInputAt input pc remaining /\
    candidateDecodeItem remaining =
      candidateSuccess isList headerLength payloadLength /\
    binaryWrapCase headerLength payloadLength
      ((headerLength + payloadLength) mod word64Modulus).

Lemma hostileNestedWrapOccurs : nestedWrapOccurs fittingOuterHeader.
Proof.
  exists 0x800d5d34, hostileNestedHeader, false, 9,
    (word64Modulus - 1).
  vm_compute; repeat split; eauto; try congruence.
  eexists; split; [reflexivity | right; left; reflexivity].
Qed.
