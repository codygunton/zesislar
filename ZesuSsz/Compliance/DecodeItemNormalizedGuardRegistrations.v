Require Import ZesuSsz.Automation.All.
From Coq Require Import List ZArith Lia.
From stdpp Require Import bitvector.definitions.
From lithium Require Import simpl_classes.
Require Import SailStdpp.MachineWord.
Require Import EvmSailRlp.evm_rlp_types.
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Contracts.RlpDecodeItem.
Require Import ZesuSsz.Contracts.RlpDecodeItemContract.
Require Import ZesuSsz.Contracts.DecodeItemReturnFacts.
Require Import ZesuSsz.Compliance.DecodeItemSailIntroduction.
Require Import ZesuSsz.Compliance.DecodeItemSemanticIntroduction.
Require Import ZesuSsz.Compliance.DecodeItemLoadedEntryFacts.
Open Scope Z_scope.

(* Retain semantic facts after generic branch normalization. *)
Ltac decodeItemNormalizedGuardBranch candidate args prefix rest :=
  match goal with
  | Hhead : decodeItemInputHead args prefix rest |- _ =>
      let domain := match goal with
        | Hdomain : decodeItemC1BDomain args |- _ => constr:(Hdomain)
        | Hdomain : decodeItemDomainAt _ decodeItemC1BDomain args |- _ => constr:(proj2 Hdomain)
        end in
      unfold SimplAnd; split;
      [intros _; eapply (candidate args prefix rest);
        [exact domain | exact Hhead | split; assumption |];
       let Hlength := fresh "HlengthBounds" in
       pose proof (decodeItemDomainInputLengthBounds args domain) as Hlength;
       let Hcast := fresh "HlengthCast" in
       assert (Hcast : bv_unsigned (Z_to_bv 64 (decodeItemInputLength args)) =
         decodeItemInputLength args) by
         (apply Z_to_bv_small; unfold bv_modulus; lia);
       rewrite <- (proj1 domain);
       first
       [ match goal with
         | Hguard : ~ ?left >= ?limit |- _ =>
           let Hnormalized := fresh "HnormalizedGuard" in
           pose proof Hguard as Hnormalized;
           try rewrite Hcast in Hnormalized;
           match goal with Hvalue : bv_unsigned ?register = bv_unsigned prefix |- _ =>
             try rewrite Hvalue in Hnormalized end;
           apply Znot_ge_lt in Hnormalized;
           rewrite Z.add_1_l; apply Z.le_succ_l; exact Hnormalized
         end
       | match goal with
         | Hguard : ?left >= ?limit |- _ =>
           let Hnormalized := fresh "HnormalizedGuard" in
           pose proof Hguard as Hnormalized;
           try rewrite Hcast in Hnormalized;
           match goal with Hvalue : bv_unsigned ?register = bv_unsigned prefix |- _ =>
             try rewrite Hvalue in Hnormalized end;
           rewrite Z.add_1_l; apply (proj2 (Z.lt_succ_r _ _)); exact (Z.ge_le _ _ Hnormalized)
         end ]
      | intros _; exact I]
  end.
#[export] Hint Extern 0
  (SimplAnd (decodeItemAcceptedFacts ?args false 1 (bv_unsigned ?prefix - 128)) True) =>
  match goal with Hhead : decodeItemInputHead args prefix ?rest |- _ =>
    decodeItemNormalizedGuardBranch decodeItemShortStringAccepted args prefix rest
  end : typeclass_instances.
#[export] Hint Extern 0 (SimplAnd (decodeItemRejectedFacts ?args) True) =>
  match goal with Hhead : decodeItemInputHead args ?prefix ?rest |- _ =>
    decodeItemNormalizedGuardBranch decodeItemShortStringRejected args prefix rest
  end : typeclass_instances.

#[export] Hint Extern 0
  (SimplAnd (decodeItemAcceptedFacts ?args true 1 (bv_unsigned ?prefix - 192)) True) =>
  match goal with Hhead : decodeItemInputHead args prefix ?rest |- _ =>
    decodeItemNormalizedGuardBranch decodeItemShortListAccepted args prefix rest
  end : typeclass_instances.
#[export] Hint Extern 0 (SimplAnd (decodeItemRejectedFacts ?args) True) =>
  match goal with Hhead : decodeItemInputHead args ?prefix ?rest |- _ =>
    decodeItemNormalizedGuardBranch decodeItemShortListRejected args prefix rest
  end : typeclass_instances.

#[export] Hint Extern 0 (SimplAnd (decodeItemRejectedFacts ?args) True) =>
  match goal with Hhead : decodeItemInputHead args ?prefix ?rest |- _ =>
    decodeItemNormalizedGuardBranch decodeItemLongStringHeaderRejected args prefix rest
  end : typeclass_instances.

(* This registration retains the existing semantic read-bound obligation. *)
#[export] Hint Extern 0 (SimplAnd (?requested < decodeItemInputLength ?args) True) =>
  match goal with
  | Hhead : decodeItemInputHead args ?prefix ?rest,
    Hvalue : bv_unsigned ?register = bv_unsigned ?prefix,
    Hguard : ~ ?left >= ?limit |- _ =>
    let domain := match goal with
      | Hdomain : decodeItemC1BDomain args |- _ => constr:(Hdomain)
      | Hdomain : decodeItemDomainAt _ decodeItemC1BDomain args |- _ => constr:(proj2 Hdomain)
      end in
    unfold SimplAnd; split;
    [ intros _;
      let Hlength := fresh "HlengthBounds" in
      pose proof (decodeItemDomainInputLengthBounds args domain) as Hlength;
      let Hcast := fresh "HlengthCast" in
      assert (Hcast : bv_unsigned (Z_to_bv 64 (decodeItemInputLength args)) =
        decodeItemInputLength args) by (apply Z_to_bv_small; unfold bv_modulus; lia);
      let Hnormalized := fresh "HnormalizedGuard" in
      pose proof Hguard as Hnormalized;
      try rewrite Hcast in Hnormalized;
      try rewrite Hvalue in Hnormalized;
      exact (Znot_ge_lt _ _ Hnormalized)
    | intros _; exact I ]
  end : typeclass_instances.

#[export] Hint Extern 0 (SimplAnd (decodeItemRejectedFacts ?args) True) =>
  match goal with Hhead : decodeItemInputHead args ?prefix ?rest |- _ =>
    decodeItemNormalizedGuardBranch decodeItemLongListHeaderRejected args prefix rest
  end : typeclass_instances.

#[export] Hint Extern 0 (SimplAnd (decodeItemAcceptedFacts ?args false 1 0) True) =>
  match goal with
  | Hhead : decodeItemInputHead args ?prefix ?rest,
    Hprefix : bv_unsigned ?prefix = 128 |- _ =>
    let domain := match goal with
      | Hdomain : decodeItemC1BDomain args |- _ => constr:(Hdomain)
      | Hdomain : decodeItemDomainAt _ decodeItemC1BDomain args |- _ => constr:(proj2 Hdomain)
      end in
    unfold SimplAnd; split;
    [intros _; exact (decodeItemEmptyAccepted args prefix rest domain Hhead Hprefix)
    | intros _; exact I]
  end : typeclass_instances.
#[export] Hint Extern 0 (SimplAnd (129 <= bv_unsigned ?prefix) True) =>
  match goal with
  | Hlower : 128 <= bv_unsigned prefix,
    Hdifferent : bv_unsigned prefix <> 128 |- _ =>
    unfold SimplAnd; split;
    [intros _; change (Z.succ 128 <= bv_unsigned prefix);
      apply (proj2 (Z.le_succ_l 128 (bv_unsigned prefix)));
     destruct (proj1 (Z.lt_eq_cases 128 (bv_unsigned prefix)) Hlower) as [Hlt | Heq];
       [exact Hlt | exfalso; apply Hdifferent; symmetry; exact Heq]
    | intros _; exact I]
  end : typeclass_instances.

(* These registrations retain the input-head meaning after generic sign normalization. *)
#[export] Hint Extern 0 (SimplAnd (128 <= bv_unsigned ?prefix) True) =>
  match goal with
  | Hhead : decodeItemInputHead ?args prefix ?rest,
    Hlookup : decodeItemInputBytes ?args !! 0%nat = Some ?loaded,
    Hbound : 128 <= bv_unsigned ?loaded |- _ =>
    let Hequal := constr:(decodeItemLoadedEntryByte args prefix rest loaded Hhead Hlookup) in
    unfold SimplAnd; split;
    [intros _; rewrite Hequal in Hbound; exact Hbound | intros _; exact I]
  end : typeclass_instances.
#[export] Hint Extern 0 (SimplAnd (bv_unsigned ?prefix <= 127) True) =>
  match goal with
  | Hhead : decodeItemInputHead ?args prefix ?rest,
    Hlookup : decodeItemInputBytes ?args !! 0%nat = Some ?loaded,
    Hbound : ~ 128 <= bv_unsigned ?loaded |- _ =>
    let Hequal := constr:(decodeItemLoadedEntryByte args prefix rest loaded Hhead Hlookup) in
    unfold SimplAnd; split;
    [intros _; rewrite Hequal in Hbound;
     apply (proj1 (Z.lt_succ_r _ 127));
     exact (Z.gt_lt _ _ (Znot_le_gt _ _ Hbound))
    | intros _; exact I]
  end : typeclass_instances.
#[export] Hint Extern 0 (SimplAnd (decodeItemAcceptedFacts ?args false 0 1) True) =>
  match goal with
  | Hhead : decodeItemInputHead args ?prefix ?rest |- _ =>
    let domain := match goal with
      | Hdomain : decodeItemC1BDomain args |- _ => constr:(Hdomain)
      | Hdomain : decodeItemDomainAt _ decodeItemC1BDomain args |- _ => constr:(proj2 Hdomain)
      end in
    unfold SimplAnd; split;
    [intros _;
     first
     [ match goal with Hplain : bv_unsigned prefix <= 127 |- _ =>
         exact (decodeItemLiteralAccepted args prefix rest domain Hhead Hplain)
       end
     | let Hclass := constr:(_ : SimplAnd (bv_unsigned prefix <= 127) True) in
       exact (decodeItemLiteralAccepted args prefix rest domain Hhead ((proj1 Hclass) I)) ]
    | intros _; exact I]
  end : typeclass_instances.
