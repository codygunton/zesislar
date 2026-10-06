Require Import ZesuSsz.Automation.All.
Require Import ZesuSsz.Automation.ByteFold.
Require Import isla.riscv64.riscv64.
From Coq Require Import List ZArith Lia.
Require Import ZesuSsz.Contracts.RlpDecodeItem.
Require Import ZesuSsz.Contracts.RlpDecodeItemContract.
Require Import ZesuSsz.Contracts.RlpDecodeItemByteFold.
Require Import ZesuSsz.Contracts.RlpDecodeItemByteFoldBlocks.
Require Import ZesuSsz.Contracts.RlpDecodeItemFoldEntries.
Require Import ZesuSsz.Contracts.DecodeItemBranchEntries.
Require Import ZesuSsz.Contracts.DecodeItemReturnFacts.
Require Import ZesuSsz.Contracts.RlpDecodeItemBlockEntries.
Require Import ZesuSsz.Contracts.ResultImage.
Require Import ZesuSsz.Compliance.DecodeItemHeaderWitnessFacts.
Require Import ZesuSsz.Compliance.DecodeItemFoldBackEdgeWitnesses.
Require Import ZesuSsz.Proofs.DecodeItem.ByteFoldPure.
Require Import ZesuSsz.Automation.Switches.PureFactHints.
Import ListNotations.
Open Scope Z_scope.

Lemma decodeItemFoldArrayIndex args n i payloadStart bytes :
  decodeItemByteFoldFacts args n i payloadStart bytes ->
  Z.of_nat (Z.to_nat (1 + i)) =
    (payloadStart + i + 0 - decodeItemInputPointer args) `div` 1.
Proof.
  intros (_ & Hi & Hstart & _). rewrite Z.div_1_r. rewrite Z2Nat.id; lia.
Qed.

Lemma decodeItemFoldSteppedCursor args n i payloadStart bytes :
  decodeItemByteFoldFacts args n i payloadStart bytes ->
  (Z_to_bv 64 (payloadStart + i) + 1)%bv =
    Z_to_bv 64 (payloadStart + (i + 1)).
Proof. intros _. bv_solve. Qed.

Lemma decodeItemFoldByteAtSuccessor args n i payloadStart bytes next :
  decodeItemByteFoldFacts args n i payloadStart bytes -> i < n ->
  nth_error (decodeItemInputBytes args) (Z.to_nat (1 + i)) = Some next ->
  nth_error bytes (Z.to_nat i) = Some next.
Proof.
  intros (_ & Hi & Hstart & Hbytes & Hlength & _) Hguard Hnext.
  rewrite Hbytes. assert (Hindex : (Z.to_nat i < Z.to_nat n)%nat) by lia.
  rewrite (nth_error_firstn_inside (skipn 1 (decodeItemInputBytes args)) (Z.to_nat n) (Z.to_nat i) Hindex).
  rewrite nth_error_skipn_offset.
  replace (1 + Z.to_nat i)%nat with (Z.to_nat (1 + i)) by lia.
  exact Hnext.
Qed.

Lemma decodeItemFoldSteppedAccumulator args n i payloadStart bytes next :
  decodeItemByteFoldFacts args n i payloadStart bytes -> i < n ->
  nth_error (decodeItemInputBytes args) (Z.to_nat (1 + i)) = Some next ->
  bv_or (Z_to_bv 64 (bigEndian (firstn (Z.to_nat i) bytes)) ≪ 8)
    (bv_zero_extend 64 next) =
  Z_to_bv 64 (bigEndian (firstn (Z.to_nat (i + 1)) bytes)).
Proof.
  intros Hfold Hguard Hnext.
  pose proof (decodeItemFoldByteAtSuccessor args n i payloadStart bytes next
    Hfold Hguard Hnext) as Hbyte.
  pose proof (decodeItem_fold_preservation args n i payloadStart bytes next
    Hfold Hguard Hbyte) as [_ Hvalue].
  rewrite Hvalue.
  assert (Hland : Z.land
    (bv_unsigned (Z_to_bv 64 (bigEndian (firstn (Z.to_nat i) bytes)) ≪ 8))
    (bv_unsigned (bv_zero_extend 64 next)) = 0).
  { bv_simplify. bitblast as index. all: (f_equal; lia). }
  apply bv_eq. rewrite bv_or_unsigned.
  rewrite -Z.add_nocarry_lor; last exact Hland. bv_solve.
Qed.

Lemma decodeItemLengthBytesValueRange (bytes : list byte) :
  0 <= bigEndian bytes < 256 ^ Z.of_nat (length bytes).
Proof.
  induction bytes using rev_ind.
  - unfold bigEndian. simpl. lia.
  - rewrite zesu_bigEndian_snoc app_length. simpl.
    rewrite Nat2Z.inj_add. simpl.
    rewrite Z.pow_add_r; try lia.
    pose proof (bv_unsigned_in_range 8 x) as Hbyte.
    change (0 <= bv_unsigned x < 256) in Hbyte.
    simpl. nia.
Qed.

Lemma decodeItemCompletedFoldValueBounds args n payloadStart bytes :
  decodeItemByteFoldFacts args n n payloadStart bytes ->
  0 <= bigEndian bytes < word64Modulus.
Proof.
  intros (Hwidth & Hi & Hstart & Hbytes & Hlength & Hfits).
  pose proof (decodeItemLengthBytesValueRange bytes) as Hvalue.
  rewrite Hlength in Hvalue.
  assert (Hpower : 256 ^ n <= 256 ^ 8) by (apply Z.pow_le_mono_r; lia).
  unfold word64Modulus. change (0 <= bigEndian bytes < 18446744073709551616).
  change (256 ^ n <= 18446744073709551616) in Hpower. lia.
Qed.

#[export] Instance decodeItemStringSliceWitness
    `{!islaG Sigma} `{!threadG}
    args (prefix : byte) (rest frameBytes : list byte) (oldAcc oldCursor loaded : bv 64) :
  @ZesuPureFactAnchor Sigma
    (∃ (n payloadStart : Z) (lengthBytes frameBytes : list byte)
       (oldAcc oldCursor loaded : bv 64) (prefix : byte) (rest : list byte),
      decodeItemEntryAt800d6a14 args n payloadStart lengthBytes frameBytes
        oldAcc oldCursor loaded prefix rest)%I
    (decodeItemFoldInitResources args (bv_unsigned prefix - 183) (decodeItemInputPointer args + 1) (firstn (Z.to_nat (bv_unsigned prefix - 183)) rest)
      frameBytes oldAcc oldCursor loaded)
    (⌜decodeItemC1BDomain args /\
      decodeItemFoldProvenance args false prefix rest (bv_unsigned prefix - 183) (decodeItemInputPointer args + 1) (firstn (Z.to_nat (bv_unsigned prefix - 183)) rest) /\
      bv_unsigned (Z_to_bv 64 (bv_unsigned prefix - 183)) < bv_unsigned (Z_to_bv 64 (decodeItemInputLength args)) /\
      decodeItemSavedFrameFacts args frameBytes⌝ ∗
     decodeItemFoldInitResources args (bv_unsigned prefix - 183) (decodeItemInputPointer args + 1) (firstn (Z.to_nat (bv_unsigned prefix - 183)) rest)
       frameBytes oldAcc oldCursor loaded ∗ decodeItemBranchContinuation args)%I.
Proof.
  unfold ZesuPureFactAnchor, ZesuPureFactIntro.
  iIntros "(%Hfacts & Hinit & Hcont)".
  iExists (bv_unsigned prefix - 183), (decodeItemInputPointer args + 1), (firstn (Z.to_nat (bv_unsigned prefix - 183)) rest), frameBytes, oldAcc, oldCursor, loaded, prefix, rest.
  unfold decodeItemEntryAt800d6a14. iFrame. iPureIntro. exact Hfacts.
Qed.

#[export] Instance decodeItemListSliceWitness
    `{!islaG Sigma} `{!threadG}
    args (prefix : byte) (rest frameBytes : list byte) (oldAcc oldCursor loaded : bv 64) :
  @ZesuPureFactAnchor Sigma
    (∃ (n payloadStart : Z) (lengthBytes frameBytes : list byte)
       (oldAcc oldCursor loaded : bv 64) (prefix : byte) (rest : list byte),
      decodeItemEntryAt800d6ab4 args n payloadStart lengthBytes frameBytes
        oldAcc oldCursor loaded prefix rest)%I
    (decodeItemFoldInitResources args (bv_unsigned prefix - 247) (decodeItemInputPointer args + 1) (firstn (Z.to_nat (bv_unsigned prefix - 247)) rest)
      frameBytes oldAcc oldCursor loaded)
    (⌜decodeItemC1BDomain args /\
      decodeItemFoldProvenance args true prefix rest (bv_unsigned prefix - 247) (decodeItemInputPointer args + 1) (firstn (Z.to_nat (bv_unsigned prefix - 247)) rest) /\
      bv_unsigned (Z_to_bv 64 (bv_unsigned prefix - 247)) < bv_unsigned (Z_to_bv 64 (decodeItemInputLength args)) /\
      decodeItemSavedFrameFacts args frameBytes⌝ ∗
     decodeItemFoldInitResources args (bv_unsigned prefix - 247) (decodeItemInputPointer args + 1) (firstn (Z.to_nat (bv_unsigned prefix - 247)) rest)
       frameBytes oldAcc oldCursor loaded ∗ decodeItemBranchContinuation args)%I.
Proof.
  unfold ZesuPureFactAnchor, ZesuPureFactIntro.
  iIntros "(%Hfacts & Hinit & Hcont)".
  iExists (bv_unsigned prefix - 247), (decodeItemInputPointer args + 1), (firstn (Z.to_nat (bv_unsigned prefix - 247)) rest), frameBytes, oldAcc, oldCursor, loaded, prefix, rest.
  unfold decodeItemEntryAt800d6ab4. iFrame. iPureIntro. exact Hfacts.
Qed.

Lemma decodeItemFoldArrayIndexWitness `{!islaG Sigma}
    args n i payloadStart bytes (continuation : nat -> iProp Sigma) :
  @ZesuPureFactIntro Sigma
    (∃ index : nat,
      ⌜Z.of_nat index = (payloadStart + i + 0 - decodeItemInputPointer args) `div` 1⌝ ∗
      continuation index)%I
    (⌜decodeItemByteFoldFacts args n i payloadStart bytes⌝ ∗
      continuation (Z.to_nat (1 + i)))%I.
Proof.
  unfold ZesuPureFactIntro. iIntros "[%Hfold Hcontinuation]".
  iExists (Z.to_nat (1 + i)). iFrame. iPureIntro.
  exact (decodeItemFoldArrayIndex args n i payloadStart bytes Hfold).
Qed.

#[export] Hint Extern 1
  (SimplAnd ((Z_to_bv 64 (?payloadStart + ?i) + 1)%bv =
    Z_to_bv 64 (?payloadStart + (?i + 1))) True) =>
  match goal with Hfold : decodeItemByteFoldFacts ?args ?n i payloadStart ?bytes |- _ =>
    unfold SimplAnd; split;
    [intros _; exact (decodeItemFoldSteppedCursor args n i payloadStart bytes Hfold)
    | intros _; exact I]
  end : typeclass_instances.

#[export] Hint Extern 1
  (SimplAnd (bv_or (Z_to_bv 64 (bigEndian (firstn (Z.to_nat ?i) ?bytes)) ≪ 8)
    (bv_zero_extend 64 ?next) =
    Z_to_bv 64 (bigEndian (firstn (Z.to_nat (?i + 1)) ?bytes))) True) =>
  match goal with Hfold : decodeItemByteFoldFacts ?args ?n i ?payloadStart bytes,
    Hguard : i < ?n,
    Hnext : nth_error (decodeItemInputBytes ?args) (Z.to_nat (1 + i)) = Some next |- _ =>
    unfold SimplAnd; split;
    [intros _; exact (decodeItemFoldSteppedAccumulator args n i payloadStart bytes next
      Hfold Hguard Hnext) | intros _; exact I]
  end : typeclass_instances.

Definition decodeItemCompletedFoldLocals args n payloadStart bytes frameBytes loaded :
    DecodeItemReturnLocals :=
  {| returnA1 := Z_to_bv 64 (payloadStart + n);
     returnA2 := Z_to_bv 64 (decodeItemInputLength args);
     returnA3 := Z_to_bv 64 (bigEndian bytes);
     returnA4 := Z_to_bv 64 (bigEndian bytes + n + 1);
     returnA5 := Z_to_bv 64 (payloadStart + n);
     returnA6 := loaded;
     returnStorage := decodeItemBeforeStorage args;
     returnFrame := frameBytes |}.

Lemma decodeItemCompletedFoldWordValues args n payloadStart bytes :
  decodeItemC1BDomain args ->
  decodeItemByteFoldFacts args n n payloadStart bytes ->
  bv_unsigned (Z_to_bv 64 (payloadStart + n)) = decodeItemInputPointer args + (1 + n) /\
  bv_unsigned (Z_to_bv 64 (bigEndian bytes)) = bigEndian bytes /\
  bv_unsigned (Z_to_bv 64 (bigEndian bytes + n + 1)) =
    ((1 + n + bigEndian bytes) mod word64Modulus).
Proof.
  intros Hdomain Hfold.
  pose proof (decodeItemCompletedFoldValueBounds args n payloadStart bytes Hfold) as Hvalue.
  destruct Hfold as (Hwidth & Hi & Hstart & Hbytes & Hlength & Hfits).
  destruct Hdomain as (Hinput & Hstorage & Hlayout).
  destruct Hlayout as (Hpointer & HlengthRange & Hnowrap & _).
  assert (Hcursor : 0 <= payloadStart + n < bv_modulus 64) by
    (unfold word64Modulus, bv_modulus in *; simpl in *; lia).
  assert (Hpayload : 0 <= bigEndian bytes < bv_modulus 64) by
    (unfold word64Modulus, bv_modulus in *; simpl in *; lia).
  rewrite (Z_to_bv_small 64 _ Hcursor) (Z_to_bv_small 64 _ Hpayload) Z_to_bv_unsigned.
  unfold word64Modulus, bv_modulus. simpl. split; first lia.
  split; first reflexivity. unfold bv_wrap, bv_modulus. simpl. f_equal. lia.
Qed.

Lemma decodeItemStringReturnLengthWitness
    `{!islaG Sigma} `{!threadG}
    args (prefix : byte) (rest : list byte) n payloadStart bytes frameBytes (loaded : bv 64) :
  @ZesuPureFactAnchor Sigma
    (∃ (locals : DecodeItemReturnLocals) (prefix : byte) (rest : list byte)
       (headerLength payloadLength : Z),
      decodeItemEntryAt800d6a40 args locals prefix rest headerLength payloadLength)%I
    (decodeItemFoldCheckedResources args n payloadStart bytes frameBytes loaded)
    (⌜decodeItemDomainAt (decodeItemReturnAddress args) decodeItemC1BDomain args /\
      decodeItemSavedFrameFacts args frameBytes /\
      decodeItemFoldProvenance args false prefix rest n payloadStart bytes /\
      decodeItemByteFoldFacts args n n payloadStart bytes /\
      decodeItemFoldLengthFits args n bytes = true⌝ ∗
     decodeItemFoldCheckedResources args n payloadStart bytes frameBytes loaded ∗
     decodeItemBranchContinuation args)%I.
Proof.
  unfold ZesuPureFactAnchor, ZesuPureFactIntro.
  iIntros "(%Hfacts & Hchecked & Hcont)".
  destruct Hfacts as (Hdomain & Hframe & Hprovenance & Hfold & Hguard).
  pose proof (decodeItemCompletedFoldAcceptedWitnessFacts args false prefix rest n payloadStart bytes
    (proj2 Hdomain) Hprovenance Hfold Hguard) as Haccepted.
  pose proof (decodeItemCompletedFoldWordValues args n payloadStart bytes
    (proj2 Hdomain) Hfold) as (Hcursor & Hpayload & Hconsumed).
  pose proof (decodeItemCompletedFoldValueBounds args n payloadStart bytes Hfold) as Hvalue.
  destruct Hprovenance as (Hhead & Hclass & Hn & Hstart & Hbytes).
  pose proof (proj2 Hdomain) as Hwellformed.
  destruct Hwellformed as (Hinput & Hstorage & Hlayout).
  iExists (decodeItemCompletedFoldLocals args n payloadStart bytes frameBytes loaded),
    prefix, rest, (1 + n), (bigEndian bytes).
  unfold decodeItemEntryAt800d6a40, decodeItemReturnEntryCore, decodeItemCompletedFoldLocals.
  unfold decodeItemFoldCheckedResources. simpl.
  iDestruct "Hchecked" as "(Hsys & H10 & H11 & H12 & H13 & H14 & H15 & H16 & H2 & H1 & H8 & Hin & Hout & Hstack & %HfoldFacts & _)".
  iFrame "Hsys H10 H11 H12 H13 H14 H15 H16 H2 H1 H8 Hin Hout Hstack Hcont". iSplit.
  - iPureIntro. split; [exact Hdomain | split; [exact Hframe | exact Hstorage]].
  - iPureIntro. repeat first [assumption | reflexivity | lia | split].
    + rewrite Hn. reflexivity.
    + rewrite Hbytes Hn. reflexivity.
Qed.

Lemma decodeItemListReturnLengthWitness
    `{!islaG Sigma} `{!threadG}
    args (prefix : byte) (rest : list byte) n payloadStart bytes frameBytes (loaded : bv 64) :
  @ZesuPureFactAnchor Sigma
    (∃ (locals : DecodeItemReturnLocals) (prefix : byte) (rest : list byte)
       (headerLength payloadLength : Z),
      decodeItemEntryAt800d6b08 args locals prefix rest headerLength payloadLength)%I
    (decodeItemFoldCheckedResources args n payloadStart bytes frameBytes loaded)
    (⌜decodeItemDomainAt (decodeItemReturnAddress args) decodeItemC1BDomain args /\
      decodeItemSavedFrameFacts args frameBytes /\
      decodeItemFoldProvenance args true prefix rest n payloadStart bytes /\
      decodeItemByteFoldFacts args n n payloadStart bytes /\
      decodeItemFoldLengthFits args n bytes = true⌝ ∗
     decodeItemFoldCheckedResources args n payloadStart bytes frameBytes loaded ∗
     decodeItemBranchContinuation args)%I.
Proof.
  unfold ZesuPureFactAnchor, ZesuPureFactIntro.
  iIntros "(%Hfacts & Hchecked & Hcont)".
  destruct Hfacts as (Hdomain & Hframe & Hprovenance & Hfold & Hguard).
  pose proof (decodeItemCompletedFoldAcceptedWitnessFacts args true prefix rest n payloadStart bytes
    (proj2 Hdomain) Hprovenance Hfold Hguard) as Haccepted.
  pose proof (decodeItemCompletedFoldWordValues args n payloadStart bytes
    (proj2 Hdomain) Hfold) as (Hcursor & Hpayload & Hconsumed).
  pose proof (decodeItemCompletedFoldValueBounds args n payloadStart bytes Hfold) as Hvalue.
  destruct Hprovenance as (Hhead & Hclass & Hn & Hstart & Hbytes).
  pose proof (proj2 Hdomain) as Hwellformed.
  destruct Hwellformed as (Hinput & Hstorage & Hlayout).
  iExists (decodeItemCompletedFoldLocals args n payloadStart bytes frameBytes loaded),
    prefix, rest, (1 + n), (bigEndian bytes).
  unfold decodeItemEntryAt800d6b08, decodeItemReturnEntryCore, decodeItemCompletedFoldLocals.
  unfold decodeItemFoldCheckedResources. simpl.
  iDestruct "Hchecked" as "(Hsys & H10 & H11 & H12 & H13 & H14 & H15 & H16 & H2 & H1 & H8 & Hin & Hout & Hstack & %HfoldFacts & _)".
  iFrame "Hsys H10 H11 H12 H13 H14 H15 H16 H2 H1 H8 Hin Hout Hstack Hcont". iSplit.
  - iPureIntro. split; [exact Hdomain | split; [exact Hframe | exact Hstorage]].
  - iPureIntro. repeat first [assumption | reflexivity | lia | split].
    + rewrite Hn. reflexivity.
    + rewrite Hbytes Hn. reflexivity.
Qed.

#[export] Hint Extern 1
  (@ZesuPureFactIntro ?Sigma
    (∃ index : nat,
      ⌜Z.of_nat index = (?payloadStart + ?i + 0 - decodeItemInputPointer ?args) `div` 1⌝ ∗
      ?continuation index)%I _) =>
  match goal with Hfold : decodeItemByteFoldFacts args ?n i payloadStart ?bytes |- _ =>
    exact (@decodeItemFoldArrayIndexWitness Sigma _ args n i payloadStart bytes continuation)
  end : typeclass_instances.

#[export] Hint Extern 1
  (@ZesuPureFactAnchor ?Sigma ?target
    (decodeItemFoldCheckedResources ?args ?n ?payloadStart ?bytes ?frameBytes ?loaded) _) =>
  first [
    match goal with
    | Hprovenance : decodeItemFoldProvenance args false ?prefix ?rest n payloadStart bytes |- _ =>
      exact (@decodeItemStringReturnLengthWitness Sigma _ _ args prefix rest n payloadStart bytes frameBytes loaded)
    end
  | match goal with
    | Hprovenance : decodeItemFoldProvenance args true ?prefix ?rest n payloadStart bytes |- _ =>
      exact (@decodeItemListReturnLengthWitness Sigma _ _ args prefix rest n payloadStart bytes frameBytes loaded)
    end ] : typeclass_instances.

Print Assumptions decodeItemFoldArrayIndex.
Print Assumptions decodeItemFoldSteppedCursor.
Print Assumptions decodeItemFoldByteAtSuccessor.
Print Assumptions decodeItemFoldSteppedAccumulator.
Print Assumptions decodeItemLengthBytesValueRange.
Print Assumptions decodeItemCompletedFoldValueBounds.
Print Assumptions decodeItemCompletedFoldWordValues.
Print Assumptions decodeItemStringSliceWitness.
Print Assumptions decodeItemListSliceWitness.
Print Assumptions decodeItemFoldArrayIndexWitness.
Print Assumptions decodeItemStringReturnLengthWitness.
Print Assumptions decodeItemListReturnLengthWitness.
