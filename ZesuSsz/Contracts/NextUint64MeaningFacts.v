(* Applies the exit lemmas of ZesuSsz.Contracts.NextUint64ExitMeaning at the
   meaning goal of nextUint64's return join (block 0x0070):

     ∃ result : NextUint64Return,
       nextResultBytes result = <stored result bytes> /\
       <stored slice image> = nextUint64SliceImage (nextRestPointer result)
                                                   (nextRestLength result) /\
       nextUint64RootResult (nextUint64Base args) result

   and registers the step in the residual tier (the form of
   ZesuSsz/Residuals/Block800d6960.v). A block caller sees it only if it
   imports this module (the nextUint64 profile's caller_contract_requires). *)
From Coq Require Import List ZArith.
From stdpp Require Import base list bitvector.definitions.
Require Import EvmSailRlp.evm_rlp_types.
Require Import ZesuSsz.Contracts.AbiBytes.
Require Import ZesuSsz.Contracts.DecodeItemCallData.
Require Import ZesuSsz.Contracts.ParentHeaderRootFacts.
Require Import ZesuSsz.Contracts.NextUint64BlockEntries.
Require Import ZesuSsz.Contracts.NextUint64DomainRanges.
Require Import ZesuSsz.Interfaces.DecodeItem.
Require Import ZesuSsz.Contracts.NextUint64ExitMeaning.
Require ZesuSsz.Automation2.ResidualLemmas.
Open Scope Z_scope.
(* ---- applying the two lemmas at the meaning goal of the return join ---- *)

(* A word register's value: the eight stored bytes of the input pointer or
   length, read back. *)
Ltac nextUint64_word_value :=
  lazymatch goal with
  | Hd : nextUint64BoundaryDomain ?args
    |- bv_unsigned _ = nextInputPointer (nextUint64Base ?args) =>
      first [ exact (nextUint64WordOfBytes _ (nextUint64InputPointerRange args Hd))
            | exact (nextUint64SliceImageWord0 _ _ (nextUint64InputPointerRange args Hd)) ]
  | Hd : nextUint64BoundaryDomain ?args
    |- bv_unsigned _ = Z.of_nat (length (nextInputBytes (nextUint64Base ?args))) =>
      exact (nextUint64WordOfBytes _ (nextUint64InputLengthRange args Hd))
  end.

(* The stored slice image: the stores rewrote the slice's two words of the
   input image; positions are offsets from the slice pointer. *)
Ltac nextUint64_image_normal :=
  rewrite ?Z.add_simpl_l;
  change (Z.to_nat 0) with 0%nat; change (Z.to_nat 8) with 8%nat;
  unfold nextUint64SliceImage, word64Bytes;
  cbn [List.map List.seq firstn skipn app Nat.add].

Ltac nextUint64_meaning_exit :=
  lazymatch goal with
  | |- exists result : NextUint64Return,
         nextResultBytes result = _ /\ _ = _ /\ nextUint64RootResult (nextUint64Base ?args) result =>
      match goal with
      | Hcall : decodeItemCallMeaning
          (decodeItemCallDataArgs ?argv ?sp ?inputEnd _ ?before) ?after |- _ =>
          first
            [ eapply (nextUint64MeaningError args argv sp inputEnd before after);
              [ assumption | assumption | exact Hcall | nextUint64_word_value
              | assumption | reflexivity | reflexivity ]
            | eapply (nextUint64MeaningSuccess args argv sp inputEnd before after);
              [ reflexivity | reflexivity | nextUint64_image_normal; reflexivity
              | nextUint64_word_value | nextUint64_word_value
              | assumption | assumption | exact Hcall | nextUint64_word_value
              | assumption | assumption | assumption | assumption | assumption ] ]
      end
  end.

#[export] Hint Extern 1 (exists result : NextUint64Return, _) =>
  nextUint64_meaning_exit : zesu_residual.
