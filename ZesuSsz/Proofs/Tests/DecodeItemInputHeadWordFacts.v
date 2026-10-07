Require Import ZesuSsz.Automation.All.
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Contracts.RlpDecodeItemContract.
Require Import ZesuSsz.Contracts.DecodeItemReturnFacts.
Open Scope Z_scope.
Ltac root_word_registered :=
  lazymatch goal with |- ?P =>
    let evidence := constr:(_ : SimplAnd P True) in exact (proj1 evidence I)
  end.
Ltac root_word_absent P :=
  let target := constr:(SimplAnd P True) in
  assert_fails (assert target by typeclasses eauto); exact I.

Lemma rootUnsignedOff (returnAddress : Z) (args : DecodeItemArgs) :
  Z_to_bv 64 (decodeItemInputLength args) <> 0%bv ->
  True.
Proof. intros. root_word_absent (bv_unsigned (Z_to_bv 64 (decodeItemInputLength args)) <> 0). Qed.

Lemma rootHeadOff (returnAddress : Z) (args : DecodeItemArgs) :
  decodeItemDomainAt returnAddress decodeItemC1BDomain args ->
  Z_to_bv 64 (decodeItemInputLength args) <> 0%bv ->
  True.
Proof. intros. root_word_absent (exists prefix rest, decodeItemInputHead args prefix rest). Qed.

Lemma rootHeadFactsOff (returnAddress : Z) (args : DecodeItemArgs) :
  decodeItemDomainAt returnAddress decodeItemC1BDomain args ->
  Z_to_bv 64 (decodeItemInputLength args) <> 0%bv ->
  True.
Proof. intros. root_word_absent (exists prefix rest, decodeItemInputHead args prefix rest /\ bv_unsigned (Z_to_bv 64 (decodeItemInputLength args)) <> 0). Qed.

Require Import ZesuSsz.Compliance.DecodeItemInputHeadWordFacts.

Lemma rootUnsignedOn (returnAddress : Z) (args : DecodeItemArgs) :
  Z_to_bv 64 (decodeItemInputLength args) <> 0%bv ->
  (bv_unsigned (Z_to_bv 64 (decodeItemInputLength args)) <> 0).
Proof. intros. root_word_registered. Qed.

Lemma rootHeadOn (returnAddress : Z) (args : DecodeItemArgs) :
  decodeItemDomainAt returnAddress decodeItemC1BDomain args ->
  Z_to_bv 64 (decodeItemInputLength args) <> 0%bv ->
  (exists prefix rest, decodeItemInputHead args prefix rest).
Proof. intros. root_word_registered. Qed.

Lemma rootHeadFactsOn (returnAddress : Z) (args : DecodeItemArgs) :
  decodeItemDomainAt returnAddress decodeItemC1BDomain args ->
  Z_to_bv 64 (decodeItemInputLength args) <> 0%bv ->
  (exists prefix rest, decodeItemInputHead args prefix rest /\ bv_unsigned (Z_to_bv 64 (decodeItemInputLength args)) <> 0).
Proof. intros. root_word_registered. Qed.

Lemma rootUnsignedMissingWord (returnAddress : Z) (args : DecodeItemArgs) :
  True.
Proof. intros. root_word_absent (bv_unsigned (Z_to_bv 64 (decodeItemInputLength args)) <> 0). Qed.

Lemma rootHeadMissingDomain (returnAddress : Z) (args : DecodeItemArgs) :
  Z_to_bv 64 (decodeItemInputLength args) <> 0%bv ->
  True.
Proof. intros. root_word_absent (exists prefix rest, decodeItemInputHead args prefix rest). Qed.

Lemma rootHeadMissingWord (returnAddress : Z) (args : DecodeItemArgs) :
  decodeItemDomainAt returnAddress decodeItemC1BDomain args ->
  True.
Proof. intros. root_word_absent (exists prefix rest, decodeItemInputHead args prefix rest). Qed.

Lemma rootHeadFactsMissingDomain (returnAddress : Z) (args : DecodeItemArgs) :
  Z_to_bv 64 (decodeItemInputLength args) <> 0%bv ->
  True.
Proof. intros. root_word_absent (exists prefix rest, decodeItemInputHead args prefix rest /\ bv_unsigned (Z_to_bv 64 (decodeItemInputLength args)) <> 0). Qed.

Lemma rootHeadFactsMissingWord (returnAddress : Z) (args : DecodeItemArgs) :
  decodeItemDomainAt returnAddress decodeItemC1BDomain args ->
  True.
Proof. intros. root_word_absent (exists prefix rest, decodeItemInputHead args prefix rest /\ bv_unsigned (Z_to_bv 64 (decodeItemInputLength args)) <> 0). Qed.

Lemma rootHeadZero (returnAddress : Z) (args : DecodeItemArgs) :
  decodeItemDomainAt returnAddress decodeItemC1BDomain args -> Z_to_bv 64 (decodeItemInputLength args) = 0%bv -> True.
Proof. intros. root_word_absent (exists prefix rest, decodeItemInputHead args prefix rest /\ bv_unsigned (Z_to_bv 64 (decodeItemInputLength args)) <> 0). Qed.

Print Assumptions rootUnsignedOff.
Print Assumptions rootHeadOff.
Print Assumptions rootHeadFactsOff.
Print Assumptions rootUnsignedOn.
Print Assumptions rootHeadOn.
Print Assumptions rootHeadFactsOn.
Print Assumptions rootUnsignedMissingWord.
Print Assumptions rootHeadMissingDomain.
Print Assumptions rootHeadMissingWord.
Print Assumptions rootHeadFactsMissingDomain.
Print Assumptions rootHeadFactsMissingWord.
Print Assumptions rootHeadZero.
