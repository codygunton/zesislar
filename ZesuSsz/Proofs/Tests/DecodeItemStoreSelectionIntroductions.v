Require Import ZesuSsz.Automation.All.
Require Import ZesuSsz.Automation.Approved.
Require Import ZesuSsz.Compliance.DecodeItemHints.
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Contracts.RlpDecodeItem.
Require Import ZesuSsz.Contracts.RlpDecodeItemContract.
Require Import ZesuSsz.Contracts.DecodeItemReturnFacts.
Require Import ZesuSsz.Contracts.RlpDecodeItemBlockEntries.
From Coq Require Import List ZArith Lia.
Open Scope Z_scope.

Require Import ZesuSsz.Evidence.DecodeItemOutput24Selections.
Require Import ZesuSsz.Evidence.DecodeItemS152StageDIndex32.
Require Import ZesuSsz.Evidence.DecodeItemS152Selected6b08.

(* Local rules keep the guard refusal tests meaningful. *)
#[local] Instance decodeItemOutput24StoreIntroduction `{!islaG Sigma}
    args (storage : list byte) (continuation : nat -> iProp Sigma) :
  @ZesuPureFactIntro Sigma
    (⌜8%N = 8%N⌝ ∗ ∃ index : nat,
      ⌜Z.of_nat index = decodeItemOutputPointer args + 24 - decodeItemOutputPointer args⌝ ∗
      ⌜(index + N.to_nat 8 <= length storage)%nat⌝ ∗ continuation index)%I
    (⌜length storage = 40%nat⌝ ∗ ⌜0 <= decodeItemOutputPointer args⌝ ∗
      ⌜decodeItemOutputPointer args + 40 < RlpDecodeItem.word64Modulus⌝ ∗
      continuation 24%nat)%I.
Proof.
  unfold ZesuPureFactIntro. iIntros "(%Hlength & %Hlower & %Hupper & Hcontinuation)".
  pose proof (decodeItemOutput24SelectionFacts args storage Hlength Hlower Hupper) as Hselection.
  unfold decodeItemOutput24Selection in Hselection.
  destruct Hselection as (Haddress & Hindex & Hmodulus & Hword & Hbound & Hkind).
  rewrite Haddress in Hindex. cbn in Hkind.
  destruct Hkind as (Hwidth & Hbase & Hbranch).
  iSplit; first (iPureIntro; exact Hwidth).
  iExists 24%nat. iFrame. iSplit; iPureIntro; assumption.
Qed.

#[local] Instance decodeItemOutput32WordStoreIntroduction `{!islaG Sigma}
    args locals (continuation : nat -> iProp Sigma) :
  @ZesuPureFactIntro Sigma
    (⌜8%N = 8%N⌝ ∗ ∃ index : nat,
      ⌜Z.of_nat index = Z.sub (Z.add (decodeItemOutputPointer args) 32) (decodeItemOutputPointer args)⌝ ∗
      ⌜(index + N.to_nat 8 <= length (returnStorage locals))%nat⌝ ∗ continuation index)%I
    (⌜length (returnStorage locals) = 40%nat⌝ ∗ continuation 32%nat)%I.
Proof.
  unfold ZesuPureFactIntro. iIntros "(%Hlength & Hcontinuation)".
  destruct (s152_stageD_index32 args locals Hlength) as (Hwidth & index & Hindex & Hbound).
  assert (Hcanonical : index = 32%nat) by lia. subst index.
  iSplit; first (iPureIntro; exact Hwidth).
  iExists 32%nat. iFrame. iSplit; iPureIntro; assumption.
Qed.

#[local] Instance decodeItemOutput32ShortStoreIntroduction `{!islaG Sigma}
    args locals (continuation : nat -> iProp Sigma) :
  @ZesuPureFactIntro Sigma
    (⌜8%N = 8%N⌝ ∗ ∃ index : nat,
      ⌜Z.of_nat index = Z.sub (Z.add (decodeItemOutputPointer args) 32) (decodeItemOutputPointer args)⌝ ∗
      ⌜(index + N.to_nat 2 <= length (returnStorage locals))%nat⌝ ∗ continuation index)%I
    (⌜length (returnStorage locals) = 40%nat⌝ ∗ continuation 32%nat)%I.
Proof.
  unfold ZesuPureFactIntro. iIntros "(%Hlength & Hcontinuation)".
  destruct (s152_selected_6b08_pure args locals Hlength) as (Hwidth & index & Hindex & Hbound).
  assert (Hcanonical : index = 32%nat) by lia. subst index.
  iSplit; first (iPureIntro; exact Hwidth).
  iExists 32%nat. iFrame. iSplit; iPureIntro; assumption.
Qed.

#[local] Instance decodeItemOutput16ByteStoreIntroduction `{!islaG Sigma}
    args locals (continuation : nat -> iProp Sigma) :
  @ZesuPureFactIntro Sigma
    (⌜(decodeItemOutputPointer args + 16 - decodeItemOutputPointer args) mod 1 = 0⌝ ∗
      ∃ index : nat,
        ⌜Z.of_nat index = (decodeItemOutputPointer args + 16 - decodeItemOutputPointer args) / 1⌝ ∗
        ⌜(index < length (returnStorage locals))%nat⌝ ∗ continuation index)%I
    (⌜length (returnStorage locals) = 40%nat⌝ ∗ continuation 16%nat)%I.
Proof.
  unfold ZesuPureFactIntro. iIntros "(%Hlength & Hcontinuation)".
  iSplit; first (iPureIntro; apply Z.mod_1_r).
  iExists 16%nat. iFrame. iSplit; iPureIntro.
  - rewrite Z.div_1_r. cbn. lia.
  - rewrite Hlength. lia.
Qed.

Lemma decodeItemOutput24StoreIntroductionMissingLength `{!islaG Sigma}
    (args : DecodeItemArgs) (storage : list byte) (continuation : nat -> iProp Sigma)  : True.
Proof.
  let target := constr:(@ZesuPureFactIntro Sigma(⌜8%N = 8%N⌝ ∗ ∃ index : nat,
      ⌜Z.of_nat index = decodeItemOutputPointer args + 24 - decodeItemOutputPointer args⌝ ∗
      ⌜(index + N.to_nat 8 <= length storage)%nat⌝ ∗ continuation index)%I
    (⌜0 <= decodeItemOutputPointer args⌝ ∗
      ⌜decodeItemOutputPointer args + 40 < RlpDecodeItem.word64Modulus⌝ ∗
      continuation 24%nat)%I) in
  assert_fails (assert target by typeclasses eauto).
  exact I.
Qed.

Lemma decodeItemOutput24StoreIntroductionWrongWidth `{!islaG Sigma}
    (args : DecodeItemArgs) (storage : list byte) (continuation : nat -> iProp Sigma)  : True.
Proof.
  let target := constr:(@ZesuPureFactIntro Sigma(⌜64%N = 8%N⌝ ∗ ∃ index : nat,
      ⌜Z.of_nat index = decodeItemOutputPointer args + 24 - decodeItemOutputPointer args⌝ ∗
      ⌜(index + N.to_nat 8 <= length storage)%nat⌝ ∗ continuation index)%I
    (⌜length storage = 40%nat⌝ ∗ ⌜0 <= decodeItemOutputPointer args⌝ ∗
      ⌜decodeItemOutputPointer args + 40 < RlpDecodeItem.word64Modulus⌝ ∗
      continuation 24%nat)%I) in
  assert_fails (assert target by typeclasses eauto).
  exact I.
Qed.

Lemma decodeItemOutput32WordStoreIntroductionMissingLength `{!islaG Sigma}
    (args : DecodeItemArgs) (locals : DecodeItemReturnLocals) (continuation : nat -> iProp Sigma)  : True.
Proof.
  let target := constr:(@ZesuPureFactIntro Sigma(⌜8%N = 8%N⌝ ∗ ∃ index : nat,
      ⌜Z.of_nat index = Z.sub (Z.add (decodeItemOutputPointer args) 32) (decodeItemOutputPointer args)⌝ ∗
      ⌜(index + N.to_nat 8 <= length (returnStorage locals))%nat⌝ ∗ continuation index)%I
    (continuation 32%nat)%I) in
  assert_fails (assert target by typeclasses eauto).
  exact I.
Qed.

Lemma decodeItemOutput32WordStoreIntroductionWrongWidth `{!islaG Sigma}
    (args : DecodeItemArgs) (locals : DecodeItemReturnLocals) (continuation : nat -> iProp Sigma)  : True.
Proof.
  let target := constr:(@ZesuPureFactIntro Sigma(⌜64%N = 8%N⌝ ∗ ∃ index : nat,
      ⌜Z.of_nat index = Z.sub (Z.add (decodeItemOutputPointer args) 32) (decodeItemOutputPointer args)⌝ ∗
      ⌜(index + N.to_nat 8 <= length (returnStorage locals))%nat⌝ ∗ continuation index)%I
    (⌜length (returnStorage locals) = 40%nat⌝ ∗ continuation 32%nat)%I) in
  assert_fails (assert target by typeclasses eauto).
  exact I.
Qed.

Lemma decodeItemOutput32ShortStoreIntroductionMissingLength `{!islaG Sigma}
    (args : DecodeItemArgs) (locals : DecodeItemReturnLocals) (continuation : nat -> iProp Sigma)  : True.
Proof.
  let target := constr:(@ZesuPureFactIntro Sigma(⌜8%N = 8%N⌝ ∗ ∃ index : nat,
      ⌜Z.of_nat index = Z.sub (Z.add (decodeItemOutputPointer args) 32) (decodeItemOutputPointer args)⌝ ∗
      ⌜(index + N.to_nat 2 <= length (returnStorage locals))%nat⌝ ∗ continuation index)%I
    (continuation 32%nat)%I) in
  assert_fails (assert target by typeclasses eauto).
  exact I.
Qed.

Lemma decodeItemOutput32ShortStoreIntroductionWrongWidth `{!islaG Sigma}
    (args : DecodeItemArgs) (locals : DecodeItemReturnLocals) (continuation : nat -> iProp Sigma)  : True.
Proof.
  let target := constr:(@ZesuPureFactIntro Sigma(⌜64%N = 8%N⌝ ∗ ∃ index : nat,
      ⌜Z.of_nat index = Z.sub (Z.add (decodeItemOutputPointer args) 32) (decodeItemOutputPointer args)⌝ ∗
      ⌜(index + N.to_nat 2 <= length (returnStorage locals))%nat⌝ ∗ continuation index)%I
    (⌜length (returnStorage locals) = 40%nat⌝ ∗ continuation 32%nat)%I) in
  assert_fails (assert target by typeclasses eauto).
  exact I.
Qed.

Lemma decodeItemOutput16ByteStoreIntroductionMissingLength `{!islaG Sigma}
    (args : DecodeItemArgs) (locals : DecodeItemReturnLocals)
    (continuation : nat -> iProp Sigma) : True.
Proof.
  let target := constr:(@ZesuPureFactIntro Sigma
    (⌜(decodeItemOutputPointer args + 16 - decodeItemOutputPointer args) mod 1 = 0⌝ ∗
      ∃ index : nat,
        ⌜Z.of_nat index = (decodeItemOutputPointer args + 16 - decodeItemOutputPointer args) / 1⌝ ∗
        ⌜(index < length (returnStorage locals))%nat⌝ ∗ continuation index)%I
    (continuation 16%nat)%I) in
  assert_fails (assert target by typeclasses eauto).
  exact I.
Qed.

Lemma decodeItemOutput16ByteStoreIntroductionWrongOffset `{!islaG Sigma}
    (args : DecodeItemArgs) (locals : DecodeItemReturnLocals)
    (continuation : nat -> iProp Sigma) : True.
Proof.
  let target := constr:(@ZesuPureFactIntro Sigma
    (⌜(decodeItemOutputPointer args + 24 - decodeItemOutputPointer args) mod 1 = 0⌝ ∗
      ∃ index : nat,
        ⌜Z.of_nat index = (decodeItemOutputPointer args + 24 - decodeItemOutputPointer args) / 1⌝ ∗
        ⌜(index < length (returnStorage locals))%nat⌝ ∗ continuation index)%I
    (⌜length (returnStorage locals) = 40%nat⌝ ∗ continuation 16%nat)%I) in
  assert_fails (assert target by typeclasses eauto).
  exact I.
Qed.

