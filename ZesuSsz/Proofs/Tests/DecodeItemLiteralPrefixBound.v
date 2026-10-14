Require Import ZesuSsz.Automation.All.
Require Import ZesuSsz.Compliance.DecodeItemUnfoldRegistrations.
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Contracts.RlpDecodeItem.
Require Import ZesuSsz.Contracts.RlpDecodeItemContract.
Require Import ZesuSsz.Contracts.DecodeItemReturnFacts.
Require Import ZesuSsz.Contracts.DecodeItemBranchEntries.
Require Import ZesuSsz.Compliance.DecodeItemBranchGuardFacts.
Require Import ZesuSsz.Compliance.DecodeItemS40GuardFacts.
Require Import ZesuSsz.Automation.Switches.PureFactHints.
Open Scope Z_scope.

Section Off.
Local Remove Hints zesu_switch_pure_fact_hints : typeclass_instances.
Lemma literalPrefixBoundOff (prefix : byte) :
  128 <= bv_unsigned prefix -> bv_unsigned prefix <= 255 ->
  bv_and (Z_to_bv 64 (bv_signed prefix)) 255 <> 128%bv ->
  129 <= bv_unsigned prefix.
Proof.
  intros H1 H2 H9. Fail zesu_pure_fact_hints_if_enabled.
  exact (decodeItemNonemptyStringPrefixGuard prefix (conj H1 H2)
    (decodeItemNativeMaskNonempty prefix H9)).
Qed.
End Off.

Lemma literalPrefixBoundOn (prefix : byte) :
  128 <= bv_unsigned prefix -> bv_unsigned prefix <= 255 ->
  bv_and (Z_to_bv 64 (bv_signed prefix)) 255 <> 128%bv ->
  129 <= bv_unsigned prefix.
Proof. intros H1 H2 H9. zesu_pure_fact_hints_if_enabled. Qed.

Lemma literalPrefixBoundSimplAnd (prefix : byte)
    (H1 : 128 <= bv_unsigned prefix) (H2 : bv_unsigned prefix <= 255)
    (H9 : bv_and (Z_to_bv 64 (bv_signed prefix)) 255 <> 128%bv) :
  SimplAnd (129 <= bv_unsigned prefix) True.
Proof.
  let Hbound := constr:(ltac:(typeclasses eauto) : SimplAnd (129 <= bv_unsigned prefix) True) in
  lazymatch Hbound with
  | context [decodeItemNativeMaskNonempty _ _] => exact Hbound
  | _ => fail "The literal bridge did not occur in the selected proof"
  end.
Qed.

Lemma literalPrefixBoundRetained `{!islaG Sigma} `{!threadG} args
    (frameBytes : list byte) (inputPrefix : byte) (rest : list byte) :
  decodeItemInputHead args inputPrefix rest ->
  128 <= bv_unsigned inputPrefix -> bv_unsigned inputPrefix <= 255 ->
  bv_signed (Z_to_bv 64 (bv_signed inputPrefix)) < 0 ->
  decodeItemSavedFrameFacts args frameBytes ->
  decodeItemDomainAt (decodeItemReturnAddress args) decodeItemC1BDomain args ->
  bv_and (Z_to_bv 64 (bv_signed inputPrefix)) 255 <> 128%bv ->
  129 <= bv_unsigned inputPrefix.
Proof. intros H0 H1 H2 H3 H4 H5 H9. zesu_pure_fact_hints_if_enabled. Qed.

Lemma literalPrefixBoundMissingLower (prefix : byte)
    (H2 : bv_unsigned prefix <= 255)
    (H9 : bv_and (Z_to_bv 64 (bv_signed prefix)) 255 <> 128%bv) : True.
Proof.
  Fail assert (Hbound : 129 <= bv_unsigned prefix) by zesu_pure_fact_hints_if_enabled.
  exact I.
Qed.

Lemma literalPrefixBoundMissingUpper (prefix : byte)
    (H1 : 128 <= bv_unsigned prefix)
    (H9 : bv_and (Z_to_bv 64 (bv_signed prefix)) 255 <> 128%bv) : True.
Proof.
  Fail assert (Hbound : 129 <= bv_unsigned prefix) by zesu_pure_fact_hints_if_enabled.
  exact I.
Qed.

Lemma literalPrefixBoundMissingGuard (prefix : byte)
    (H1 : 128 <= bv_unsigned prefix) (H2 : bv_unsigned prefix <= 255) : True.
Proof.
  Fail assert (Hbound : 129 <= bv_unsigned prefix) by zesu_pure_fact_hints_if_enabled.
  exact I.
Qed.

Lemma literalPrefixBoundOther (prefix other : byte)
    (H1 : 128 <= bv_unsigned other) (H2 : bv_unsigned other <= 255)
    (H9 : bv_and (Z_to_bv 64 (bv_signed prefix)) 255 <> 128%bv) : True.
Proof.
  Fail assert (Hbound : 129 <= bv_unsigned other) by zesu_pure_fact_hints_if_enabled.
  exact I.
Qed.

Lemma normalizedPrefixBoundControl (prefix : byte)
    (H1 : 128 <= bv_unsigned prefix) (H2 : bv_unsigned prefix <= 255)
    (H9 : bv_and (Z_to_bv 64 (bv_signed prefix)) 255 <> Z_to_bv 64 128) :
  129 <= bv_unsigned prefix.
Proof. zesu_pure_fact_hints_if_enabled. Qed.

Print Assumptions literalPrefixBoundOff.
Print Assumptions literalPrefixBoundOn.
Print Assumptions literalPrefixBoundSimplAnd.
Print Assumptions literalPrefixBoundRetained.
Print Assumptions literalPrefixBoundMissingLower.
Print Assumptions literalPrefixBoundMissingUpper.
Print Assumptions literalPrefixBoundMissingGuard.
Print Assumptions literalPrefixBoundOther.
Print Assumptions normalizedPrefixBoundControl.
