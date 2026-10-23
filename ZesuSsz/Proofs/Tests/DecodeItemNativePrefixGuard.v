Require Import ZesuSsz.Automation.All.
Require Import ZesuSsz.Generated.DecodeItem.BootstrapRegistrations.
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Contracts.RlpDecodeItem.
Require Import ZesuSsz.Contracts.RlpDecodeItemContract.
Require Import ZesuSsz.Contracts.DecodeItemBranchEntries.
Require Import ZesuSsz.Contracts.DecodeItemReturnFacts.
Require Import ZesuSsz.Compliance.DecodeItemBranchGuardFacts.
Require Import ZesuSsz.Compliance.DecodeItemS40GuardFacts.
Require Import ZesuSsz.Automation.Switches.PureFactHints.
Open Scope Z_scope.

Section Off.
Local Remove Hints zesu_switch_pure_fact_hints : typeclass_instances.
Lemma nativePrefixMaskOff (prefix : byte) :
  bv_and (Z_to_bv 64 (bv_signed prefix)) 255 <> 128%bv ->
  bv_and (Z_to_bv 64 (bv_signed prefix)) 255 <> Z_to_bv 64 128.
Proof.
  intros H9. Fail zesu_pure_fact_hints_if_enabled.
  exact (decodeItemNativeMaskNonempty prefix H9).
Qed.
End Off.
Require Import ZesuSsz.Generated.DecodeItem.Registrations.

Lemma nativePrefixNonemptyOn (inputPrefix : byte) :
  128 <= bv_unsigned inputPrefix -> bv_unsigned inputPrefix <= 255 ->
  bv_and (Z_to_bv 64 (bv_signed inputPrefix)) 255 <> 128%bv ->
  129 <= bv_unsigned inputPrefix.
Proof.
  intros H1 H2 H9.
  assert (Hmask : bv_and (Z_to_bv 64 (bv_signed inputPrefix)) 255 <> Z_to_bv 64 128)
    by zesu_pure_fact_hints_if_enabled.
  zesu_pure_fact_hints_if_enabled.
Qed.

Lemma nativePrefixMaskOn (inputPrefix : byte) :
  bv_and (Z_to_bv 64 (bv_signed inputPrefix)) 255 <> 128%bv ->
  bv_and (Z_to_bv 64 (bv_signed inputPrefix)) 255 <> Z_to_bv 64 128.
Proof. intros H9. zesu_pure_fact_hints_if_enabled. Qed.

Lemma nativePrefixEmptyOn `{!islaG Sigma} `{!threadG} args (inputPrefix : byte)
    (rest frameBytes : list byte) :
  decodeItemInputHead args inputPrefix rest ->
  128 <= bv_unsigned inputPrefix -> bv_unsigned inputPrefix <= 255 ->
  bv_signed (Z_to_bv 64 (bv_signed inputPrefix)) < 0 ->
  decodeItemSavedFrameFacts args frameBytes ->
  decodeItemDomainAt (decodeItemReturnAddress args) decodeItemC1BDomain args ->
  bv_and (Z_to_bv 64 (bv_signed inputPrefix)) 255 = 128%bv ->
  ⊢ (⌜decodeItemInputHead args inputPrefix rest /\
    bv_unsigned inputPrefix = 128 /\
    decodeItemAcceptedFacts args false 1 0 /\
    decodeItemBeforeStorage args = decodeItemBeforeStorage args /\
    Z_to_bv 64 (decodeItemInputPointer args) = Z_to_bv 64 (decodeItemInputPointer args) /\
    Z_to_bv 64 (decodeItemInputLength args) = Z_to_bv 64 (decodeItemInputLength args)⌝ : iProp Sigma).
Proof.
  intros H0 H1 H2 H3 H4 H5 H9.
  assert (Hprefix : bv_unsigned inputPrefix = 128) by zesu_pure_fact_hints_if_enabled.
  assert (Haccepted : decodeItemAcceptedFacts args false 1 0) by zesu_pure_fact_hints_if_enabled.
  iPureIntro. tauto.
Qed.

Lemma nativePrefixOtherWitness (inputPrefix other : byte)
    (H9 : bv_and (Z_to_bv 64 (bv_signed inputPrefix)) 255 = 128%bv) : True.
Proof.
  Fail assert (Hother : bv_unsigned other = 128) by zesu_pure_fact_hints_if_enabled.
  exact I.
Qed.

Print Assumptions nativePrefixMaskOff.
Print Assumptions nativePrefixNonemptyOn.
Print Assumptions nativePrefixMaskOn.
Print Assumptions nativePrefixEmptyOn.
Print Assumptions nativePrefixOtherWitness.
