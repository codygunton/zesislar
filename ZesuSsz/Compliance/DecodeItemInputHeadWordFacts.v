Require Import ZesuSsz.Automation.All.
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Compliance.DecodeItemSemanticIntroduction.
Require Import ZesuSsz.Contracts.RlpDecodeItemContract.
Require Import ZesuSsz.Contracts.DecodeItemReturnFacts.

Lemma decodeItemInputLengthWordNonzero args :
  Z_to_bv 64 (decodeItemInputLength args) <> 0%bv ->
  bv_unsigned (Z_to_bv 64 (decodeItemInputLength args)) <> 0.
Proof.
  intros Hword Hzero. apply Hword. apply (inj bv_unsigned).
  rewrite Hzero. reflexivity.
Qed.

Lemma decodeItemWordNonzeroInputHead returnAddress args :
  decodeItemDomainAt returnAddress decodeItemC1BDomain args ->
  Z_to_bv 64 (decodeItemInputLength args) <> 0%bv ->
  exists prefix rest, decodeItemInputHead args prefix rest.
Proof.
  intros Hdomain Hword. apply (decodeItemDomainNonemptyInputHead returnAddress args Hdomain).
  exact (decodeItemInputLengthWordNonzero args Hword).
Qed.

Lemma decodeItemWordNonzeroInputHeadFacts returnAddress args :
  decodeItemDomainAt returnAddress decodeItemC1BDomain args ->
  Z_to_bv 64 (decodeItemInputLength args) <> 0%bv ->
  exists prefix rest, decodeItemInputHead args prefix rest /\
    bv_unsigned (Z_to_bv 64 (decodeItemInputLength args)) <> 0.
Proof.
  intros Hdomain Hword.
  destruct (decodeItemWordNonzeroInputHead returnAddress args Hdomain Hword)
    as [prefix [rest Hhead]].
  exists prefix, rest. split; [exact Hhead |].
  exact (decodeItemInputLengthWordNonzero args Hword).
Qed.
Print Assumptions decodeItemInputLengthWordNonzero.
Print Assumptions decodeItemWordNonzeroInputHead.
Print Assumptions decodeItemWordNonzeroInputHeadFacts.

#[export] Hint Extern 1
  (SimplAnd (bv_unsigned (Z_to_bv 64 (decodeItemInputLength ?args)) <> 0) True) =>
  match goal with
  | Hword : Z_to_bv 64 (decodeItemInputLength args) <> 0%bv |- _ =>
    unfold SimplAnd; split;
    [intros _; exact (decodeItemInputLengthWordNonzero args Hword)
    | intros _; exact I]
  end : typeclass_instances.

#[export] Hint Extern 1
  (SimplAnd (exists prefix rest, decodeItemInputHead ?args prefix rest) True) =>
  match goal with
  | Hdomain : decodeItemDomainAt ?returnAddress decodeItemC1BDomain args,
    Hword : Z_to_bv 64 (decodeItemInputLength args) <> 0%bv |- _ =>
    unfold SimplAnd; split;
    [intros _; exact (decodeItemWordNonzeroInputHead returnAddress args Hdomain Hword)
    | intros _; exact I]
  end : typeclass_instances.

#[export] Hint Extern 1
  (SimplAnd (exists prefix rest, decodeItemInputHead ?args prefix rest /\
    bv_unsigned (Z_to_bv 64 (decodeItemInputLength ?args)) <> 0) True) =>
  match goal with
  | Hdomain : decodeItemDomainAt ?returnAddress decodeItemC1BDomain args,
    Hword : Z_to_bv 64 (decodeItemInputLength args) <> 0%bv |- _ =>
    unfold SimplAnd; split;
    [intros _; exact (decodeItemWordNonzeroInputHeadFacts returnAddress args Hdomain Hword)
    | intros _; exact I]
  end : typeclass_instances.
