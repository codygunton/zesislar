Require Import ZesuSsz.Automation.All.
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Contracts.RlpDecodeItem.
Require Import ZesuSsz.Contracts.RlpDecodeItemContract.
Require Import ZesuSsz.Contracts.DecodeItemReturnFacts.
Require Import ZesuSsz.Contracts.RlpDecodeItemBlockEntries.
Require Import ZesuSsz.Evidence.DecodeItemOutput24Selections.
Require Import ZesuSsz.Evidence.DecodeItemS152StageDIndex32.
Require Import ZesuSsz.Evidence.DecodeItemS152Selected6b08.
From Coq Require Import List ZArith Lia.
Open Scope Z_scope.

#[export] Instance decodeItemOutput24StoreIntroduction `{!islaG Sigma}
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

#[export] Instance decodeItemOutput32WordStoreIntroduction `{!islaG Sigma}
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

#[export] Instance decodeItemOutput32ShortStoreIntroduction `{!islaG Sigma}
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

Print Assumptions decodeItemOutput24StoreIntroduction.
Print Assumptions decodeItemOutput32WordStoreIntroduction.
Print Assumptions decodeItemOutput32ShortStoreIntroduction.
