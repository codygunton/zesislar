Require Import ZesuSsz.Automation.All.
Require Import ZesuSsz.Generated.DecodeItem.Entries.
Require Import ZesuSsz.Generated.DecodeItem.BootstrapRegistrations.
Require Import ZesuSsz.Generated.DecodeItem.Registrations.
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Contracts.RlpDecodeItem.
Require Import ZesuSsz.Contracts.RlpDecodeItemContract.
Require Import ZesuSsz.Contracts.RlpDecodeItemByteFold.
Require Import ZesuSsz.Contracts.DecodeItemReturnFacts.
Require Import ZesuSsz.Contracts.DecodeItemBranchEntries.
Require Import ZesuSsz.Compliance.DecodeItemStringSuccessorWitnesses.
Require Import ZesuSsz.Compliance.DecodeItemFoldSuccessorWitnesses.
From Coq Require Import List ZArith Lia.
Open Scope Z_scope.

(* Conditional checks retain the pre-load frame and the pending machine trace. *)
Definition stringSuccessorEvidence `{!islaG Sigma} `{!threadG}
    args (prefix : byte) rest (n i payloadStart : Z)
    (lengthBytes frameBytes : list byte) (next : byte) (loaded : bv 64) : Prop :=
  ⊢ ((reg_col (decodeItemSysRegs args) ∗
   "x10" ↦ᵣ RVal_Bits (Z_to_bv 64 (decodeItemOutputPointer args)) ∗
   "x11" ↦ᵣ RVal_Bits (Z_to_bv 64 (payloadStart + n)) ∗
   "x12" ↦ᵣ RVal_Bits (Z_to_bv 64 (decodeItemInputLength args)) ∗
   "x13" ↦ᵣ RVal_Bits (bv_or (Z_to_bv 64 (bigEndian (firstn (Z.to_nat i) lengthBytes)) ≪ 8)
     (bv_zero_extend 64 next)) ∗
   "x14" ↦ᵣ RVal_Bits (Z_to_bv 64 (n + 1)) ∗
   "x15" ↦ᵣ RVal_Bits ((Z_to_bv 64 (payloadStart + i) + 1)%bv) ∗
   "x16" ↦ᵣ RVal_Bits loaded ∗
   "x2" ↦ᵣ RVal_Bits (Z_to_bv 64 (decodeItemStackPointer args - decodeItemStackBytes)) ∗
   "x1" ↦ᵣ RVal_Bits (Z_to_bv 64 (decodeItemReturnAddress args)) ∗
   "x8" ↦ᵣ RVal_Bits (Z_to_bv 64 (decodeItemStackPointer args)) ∗
   decodeItemInputPointer args ↦ₘ∗ decodeItemInputBytes args ∗
   decodeItemOutputPointer args ↦ₘ∗ decodeItemBeforeStorage args ∗
   (decodeItemStackPointer args - decodeItemStackBytes) ↦ₘ∗ frameBytes ∗
   ⌜length frameBytes = 16%nat /\
     decodeItemByteFoldFacts args n i payloadStart lengthBytes⌝ ∗ True) ∗
   decodeItemBranchContinuation args -∗
   decodeItemEntryAt800d6a24 args prefix rest)%I.

Lemma stringLookupConditionalFixture `{!islaG Sigma} `{!threadG}
    args (prefix : byte) rest (n i payloadStart : Z)
    (lengthBytes frameBytes : list byte) (loaded : bv 64) (n2 : byte)
    (pending : isla_trace) (preLoadFrame : iProp Sigma) :
  i < n ->
  decodeItemByteFoldFacts args n i payloadStart lengthBytes ->
  decodeItemDomainAt (decodeItemReturnAddress args) decodeItemC1BDomain args ->
  decodeItemSavedFrameFacts args frameBytes ->
  decodeItemFoldProvenance args false prefix rest n payloadStart lengthBytes ->
  (Z_to_bv 64 (payloadStart + i) + 1)%bv <> Z_to_bv 64 (payloadStart + n) ->
  ⊢ (((decodeItemInputPointer args ↦ₘ∗ decodeItemInputBytes args) ∗ preLoadFrame) ∗
    (∀ vmem : byte,
      ⌜decodeItemInputBytes args !! Z.to_nat (1 + i) = Some vmem⌝ -∗
      ⌜n2 = vmem⌝ -∗
      ⌜stringSuccessorEvidence args prefix rest n i payloadStart
          lengthBytes frameBytes vmem loaded⌝ -∗
      ((decodeItemInputPointer args ↦ₘ∗ decodeItemInputBytes args) ∗ preLoadFrame) -∗
      WPasm pending) -∗
    (find_in_context (FindMemMapsTo (bv_unsigned (Z_to_bv 64 (payloadStart + i))))
   (λ mk : mem_mapsto_kind,
      match mk with
      | MKMapsTo n' vmem => (∃ Heq : 8%N = n', ⌜eq_rect 8%N bv n2 n' Heq = vmem⌝ -∗ bv_unsigned (Z_to_bv 64 (payloadStart + i)) ↦ₘ vmem -∗ WPasm pending)%I
      | MKArray n' a' values =>
          if (n' =? 8)%N
          then
           (⌜((bv_unsigned (Z_to_bv 64 (payloadStart + i)) - a') `mod` 1)%Z = 0%Z⌝ ∗
            ∃ i0 : nat, ⌜Z.of_nat i0 = ((bv_unsigned (Z_to_bv 64 (payloadStart + i)) - a') `div` 1)%Z⌝ ∗ ⌜(i0 < length values)%nat⌝ ∗
              ∃ Heq : 8%N = n', ∀ vmem : bv n', ⌜values !! i0 = Some vmem⌝ -∗ ⌜eq_rect 8%N bv n2 n' Heq = vmem⌝ -∗ a' ↦ₘ∗ values -∗ WPasm pending)%I
          else
           (⌜n' = 8%N⌝ ∗
            ∃ i0 : nat, ⌜Z.of_nat i0 = (bv_unsigned (Z_to_bv 64 (payloadStart + i)) - a')%Z⌝ ∗ ⌜(i0 + N.to_nat 1 ≤ length values)%nat⌝ ∗
              ∀ vmem : bv 8, ⌜vmem = Z_to_bv 8 (little_endian_to_bv n' (take (N.to_nat 1) (drop i0 values)))⌝ -∗ ⌜n2 = vmem⌝ -∗ a' ↦ₘ∗ values -∗ WPasm pending)%I
      | MKUninit _ _ => False%I
      | MKMMIO a' length =>
          (⌜(a' ≤ bv_unsigned (Z_to_bv 64 (payloadStart + i)))%Z⌝ ∗ ⌜(bv_unsigned (Z_to_bv 64 (payloadStart + i)) + 1 ≤ a' + length)%Z⌝ ∗
           ∃ Pks Pks' : spec, spec_trace Pks ∗ ⌜scons (SReadMem (Z_to_bv 64 (payloadStart + i)) n2) Pks' ⊆ Pks⌝ ∗ (spec_trace Pks' -∗ WPasm pending))%I
      end)))%I.
Proof.
  intros Hguard Hfold Hdomain Hframe Hprovenance Hbranch.
  iIntros "((Hin & Hpre) & Hcallback)".
  iApply find_in_context_mem_mapsto_semantic.
  iExists (MKArray 8 (decodeItemInputPointer args) (decodeItemInputBytes args)).
  cbn [mem_mapsto_kind_prop]. iFrame "Hin".
  iSplit; [iPureIntro; apply Z.mod_1_r|].
  iExists (Z.to_nat (1 + i)). iSplit.
  { iPureIntro.
    pose proof (DecodeItemCorrectedWitnessSelections.decodeItemFoldWordArrayIndex
      args n i payloadStart lengthBytes Hdomain Hfold) as Hindex.
    replace (bv_add (Z_to_bv 64 (payloadStart + i)) 0) with
      (Z_to_bv 64 (payloadStart + i)) in Hindex by bv_solve. exact Hindex. }
  iSplit.
  { iPureIntro.
    destruct (proj2 Hdomain) as (_ & _ & Hlayout).
    unfold decodeItemEntryLayout in Hlayout.
    destruct Hfold as (_ & Hi & Hstart & _ & _ & Hbound).
    destruct Hlayout as (Hp & Hl & Hnowrap & Hrest).
    pose proof (proj1 (proj2 Hdomain)) as Hsize. cbn in Hsize. lia. }
  iExists eq_refl. iIntros (vmem) "%Hlookup %Heq Hin".
  iApply ("Hcallback" $! vmem with "[] [] [] [Hin Hpre]");
    try (iPureIntro; assumption).
  - iPureIntro. unfold stringSuccessorEvidence.
    exact (decodeItemStringSuccessorIntroduction args prefix rest n i
      payloadStart lengthBytes frameBytes vmem loaded
      Hguard Hdomain Hframe Hprovenance Hlookup Hbranch).
  - iFrame.
Qed.
Print Assumptions stringLookupConditionalFixture.

Definition listSuccessorEvidence `{!islaG Sigma} `{!threadG}
    args (prefix : byte) rest (n i payloadStart : Z)
    (lengthBytes frameBytes : list byte) (next : byte) (loaded : bv 64) : Prop :=
  ⊢ (  (reg_col (decodeItemSysRegs args) ∗
   "x10" ↦ᵣ RVal_Bits (Z_to_bv 64 (decodeItemOutputPointer args)) ∗
   "x11" ↦ᵣ RVal_Bits (Z_to_bv 64 (payloadStart + n)) ∗
   "x12" ↦ᵣ RVal_Bits (Z_to_bv 64 (decodeItemInputLength args)) ∗
   "x13" ↦ᵣ RVal_Bits (bv_or (Z_to_bv 64 (bigEndian (firstn (Z.to_nat i) lengthBytes)) ≪ 8)
     (bv_zero_extend 64 next)) ∗
   "x14" ↦ᵣ RVal_Bits (Z_to_bv 64 (n + 1)) ∗
   "x15" ↦ᵣ RVal_Bits ((Z_to_bv 64 (payloadStart + i) + 1)%bv) ∗
   "x16" ↦ᵣ RVal_Bits loaded ∗
   "x2" ↦ᵣ RVal_Bits (Z_to_bv 64 (decodeItemStackPointer args - decodeItemStackBytes)) ∗
   "x1" ↦ᵣ RVal_Bits (Z_to_bv 64 (decodeItemReturnAddress args)) ∗
   "x8" ↦ᵣ RVal_Bits (Z_to_bv 64 (decodeItemStackPointer args)) ∗
   decodeItemInputPointer args ↦ₘ∗ decodeItemInputBytes args ∗
   decodeItemOutputPointer args ↦ₘ∗ decodeItemBeforeStorage args ∗
   (decodeItemStackPointer args - decodeItemStackBytes) ↦ₘ∗ frameBytes ∗
   ⌜length frameBytes = 16%nat /\
     decodeItemByteFoldFacts args n i payloadStart lengthBytes⌝ ∗ True)%I ∗ decodeItemBranchContinuation args -∗
     decodeItemEntryAt800d6ac4 args prefix rest)%I.

Lemma listLookupConditionalFixture `{!islaG Sigma} `{!threadG}
    args (prefix : byte) rest (n i payloadStart : Z)
    (lengthBytes frameBytes : list byte) (loaded : bv 64) (n2 : byte)
    (pending : isla_trace) (preLoadFrame : iProp Sigma) :
  i < n ->
  decodeItemByteFoldFacts args n i payloadStart lengthBytes ->
  decodeItemDomainAt (decodeItemReturnAddress args) decodeItemC1BDomain args ->
  decodeItemSavedFrameFacts args frameBytes ->
  decodeItemFoldProvenance args true prefix rest n payloadStart lengthBytes ->
  (Z_to_bv 64 (payloadStart + i) + 1)%bv <> Z_to_bv 64 (payloadStart + n) ->
  ⊢ (((decodeItemInputPointer args ↦ₘ∗ decodeItemInputBytes args) ∗ preLoadFrame) ∗
    (∀ vmem : byte,
      ⌜decodeItemInputBytes args !! Z.to_nat (1 + i) = Some vmem⌝ -∗
      ⌜n2 = vmem⌝ -∗
      ⌜listSuccessorEvidence args prefix rest n i payloadStart
          lengthBytes frameBytes vmem loaded⌝ -∗
      ((decodeItemInputPointer args ↦ₘ∗ decodeItemInputBytes args) ∗ preLoadFrame) -∗
      WPasm pending) -∗
    (find_in_context (FindMemMapsTo (bv_unsigned (Z_to_bv 64 (payloadStart + i))))
   (λ mk : mem_mapsto_kind,
      match mk with
      | MKMapsTo n' vmem => (∃ Heq : 8%N = n', ⌜eq_rect 8%N bv n2 n' Heq = vmem⌝ -∗ bv_unsigned (Z_to_bv 64 (payloadStart + i)) ↦ₘ vmem -∗ WPasm pending)%I
      | MKArray n' a' values =>
          if (n' =? 8)%N
          then
           (⌜((bv_unsigned (Z_to_bv 64 (payloadStart + i)) - a') `mod` 1)%Z = 0%Z⌝ ∗
            ∃ i0 : nat, ⌜Z.of_nat i0 = ((bv_unsigned (Z_to_bv 64 (payloadStart + i)) - a') `div` 1)%Z⌝ ∗ ⌜(i0 < length values)%nat⌝ ∗
              ∃ Heq : 8%N = n', ∀ vmem : bv n', ⌜values !! i0 = Some vmem⌝ -∗ ⌜eq_rect 8%N bv n2 n' Heq = vmem⌝ -∗ a' ↦ₘ∗ values -∗ WPasm pending)%I
          else
           (⌜n' = 8%N⌝ ∗
            ∃ i0 : nat, ⌜Z.of_nat i0 = (bv_unsigned (Z_to_bv 64 (payloadStart + i)) - a')%Z⌝ ∗ ⌜(i0 + N.to_nat 1 ≤ length values)%nat⌝ ∗
              ∀ vmem : bv 8, ⌜vmem = Z_to_bv 8 (little_endian_to_bv n' (take (N.to_nat 1) (drop i0 values)))⌝ -∗ ⌜n2 = vmem⌝ -∗ a' ↦ₘ∗ values -∗ WPasm pending)%I
      | MKUninit _ _ => False%I
      | MKMMIO a' length =>
          (⌜(a' ≤ bv_unsigned (Z_to_bv 64 (payloadStart + i)))%Z⌝ ∗ ⌜(bv_unsigned (Z_to_bv 64 (payloadStart + i)) + 1 ≤ a' + length)%Z⌝ ∗
           ∃ Pks Pks' : spec, spec_trace Pks ∗ ⌜scons (SReadMem (Z_to_bv 64 (payloadStart + i)) n2) Pks' ⊆ Pks⌝ ∗ (spec_trace Pks' -∗ WPasm pending))%I
      end)))%I.
Proof.
  intros Hguard Hfold Hdomain Hframe Hprovenance Hbranch.
  iIntros "((Hin & Hpre) & Hcallback)".
  iApply find_in_context_mem_mapsto_semantic.
  iExists (MKArray 8 (decodeItemInputPointer args) (decodeItemInputBytes args)).
  cbn [mem_mapsto_kind_prop]. iFrame "Hin".
  iSplit; [iPureIntro; apply Z.mod_1_r|].
  iExists (Z.to_nat (1 + i)). iSplit.
  { iPureIntro.
    pose proof (DecodeItemCorrectedWitnessSelections.decodeItemFoldWordArrayIndex
      args n i payloadStart lengthBytes Hdomain Hfold) as Hindex.
    replace (bv_add (Z_to_bv 64 (payloadStart + i)) 0) with
      (Z_to_bv 64 (payloadStart + i)) in Hindex by bv_solve. exact Hindex. }
  iSplit.
  { iPureIntro.
    destruct (proj2 Hdomain) as (_ & _ & Hlayout).
    unfold decodeItemEntryLayout in Hlayout.
    destruct Hfold as (_ & Hi & Hstart & _ & _ & Hbound).
    destruct Hlayout as (Hp & Hl & Hnowrap & Hrest).
    pose proof (proj1 (proj2 Hdomain)) as Hsize. cbn in Hsize. lia. }
  iExists eq_refl. iIntros (vmem) "%Hlookup %Heq Hin".
  iApply ("Hcallback" $! vmem with "[] [] [] [Hin Hpre]");
    try (iPureIntro; assumption).
  - iPureIntro. unfold listSuccessorEvidence.
    exact (decodeItemListSuccessorIntroduction args prefix rest n i
      payloadStart lengthBytes frameBytes vmem loaded
      Hguard Hdomain Hframe Hprovenance Hlookup Hbranch).
  - iFrame.
Qed.
Print Assumptions listLookupConditionalFixture.
