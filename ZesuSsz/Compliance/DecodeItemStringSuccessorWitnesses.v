Require Import ZesuSsz.Automation.All.
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Contracts.RlpDecodeItem.
Require Import ZesuSsz.Contracts.RlpDecodeItemContract.
Require Import ZesuSsz.Contracts.RlpDecodeItemByteFold.
Require Import ZesuSsz.Contracts.RlpDecodeItemFoldEntries.
Require Import ZesuSsz.Contracts.DecodeItemReturnFacts.
Require Import ZesuSsz.Contracts.DecodeItemBranchEntries.
Require Import ZesuSsz.Compliance.DecodeItemJoinTransferPure.
Require Import ZesuSsz.Compliance.DecodeItemFoldExitFacts.
Require Import ZesuSsz.Compliance.DecodeItemCorrectedWitnessSelections.
From Coq Require Import List ZArith Lia.
Open Scope Z_scope.

Lemma decodeItemStringSuccessorIntroduction `{!islaG Sigma} `{!threadG}
    args (prefix : byte) rest (n i payloadStart : Z)
    (lengthBytes frameBytes : list byte) (next : byte) (loaded : bv 64) :
  i < n ->
  decodeItemDomainAt (decodeItemReturnAddress args) decodeItemC1BDomain args ->
  decodeItemSavedFrameFacts args frameBytes ->
  decodeItemFoldProvenance args false prefix rest n payloadStart lengthBytes ->
  decodeItemInputBytes args !! Z.to_nat (1 + i) = Some next ->
  (Z_to_bv 64 (payloadStart + i) + 1)%bv <> Z_to_bv 64 (payloadStart + n) ->
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
Proof.
  intros Hguard Hdomain Hframe Hprovenance Hlookup Hbranch.
  iIntros "(Hraw & Hcont)".
  iDestruct "Hraw" as "(Hregs & Ha0 & Ha1 & Ha2 & Ha3 & Ha4 & Ha5 & Ha6 & Hsp & Hra & Hs0 & Hin & Hout & Hstack & %Hfacts & _)".
  destruct Hfacts as [Hlength Hfold].
  pose proof (decodeItemByteFoldBackedgeGuard args n i payloadStart lengthBytes
    (proj2 Hdomain) Hfold Hguard Hbranch) as [Hnext _].
  pose proof Hlookup as Hnth. rewrite -decodeItemListLookupNthError in Hnth.
  pose proof (decodeItemFoldSteppedAccumulator args n i payloadStart lengthBytes next
    Hfold Hguard Hnth) as Hacc.
  pose proof (decodeItemFoldSteppedCursor args n i payloadStart lengthBytes Hfold) as Hcursor.
  iApply (decodeItemStringHeaderIntro args prefix rest n (i + 1) payloadStart
    lengthBytes frameBytes loaded Hnext Hdomain Hframe Hprovenance).
  unfold decodeItemByteFoldStringHeader, decodeItemByteFoldResources.
  rewrite -Hacc -Hcursor. iFrame "Hregs Ha0 Ha1 Ha2 Ha3 Ha4 Ha5 Ha6 Hsp Hra Hs0 Hin Hout Hstack Hcont". iPureIntro.
  unfold decodeItemByteFoldFacts in *. destruct Hfold as (Hw & Hi & Hstart & Hbytes & Hlen & Hfit).
  repeat split; try assumption; lia.
Qed.
Print Assumptions decodeItemStringSuccessorIntroduction.

#[export] Instance decodeItemStringSuccessorNamed `{!islaG Sigma} `{!threadG}
    args (prefix : byte) rest (n i payloadStart : Z)
    (lengthBytes : list byte) (next : byte) :
  @ZesuPureFactAnchor Sigma (decodeItemEntryAt800d6a24 args prefix rest)
    ("x13" ↦ᵣ RVal_Bits (bv_or
      (Z_to_bv 64 (bigEndian (firstn (Z.to_nat i) lengthBytes)) ≪ 8)
      (bv_zero_extend 64 next)))%I
    (∃ (frameBytes : list byte) (loaded : bv 64),
      ⌜i < n /\
        decodeItemDomainAt (decodeItemReturnAddress args) decodeItemC1BDomain args /\
        decodeItemSavedFrameFacts args frameBytes /\
        decodeItemFoldProvenance args false prefix rest n payloadStart lengthBytes /\
        decodeItemInputBytes args !! Z.to_nat (1 + i) = Some next /\
        (Z_to_bv 64 (payloadStart + i) + 1)%bv <> Z_to_bv 64 (payloadStart + n)⌝ ∗
      (reg_col (decodeItemSysRegs args) ∗
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
      decodeItemBranchContinuation args)%I.
Proof.
  unfold ZesuPureFactAnchor, ZesuPureFactIntro.
  iIntros "(%frameBytes & %loaded & %Hfacts & Hraw & Hcont)".
  destruct Hfacts as (Hguard & Hdomain & Hframe & Hprovenance & Hlookup & Hbranch).
  iApply (decodeItemStringSuccessorIntroduction args prefix rest n i payloadStart
    lengthBytes frameBytes next loaded Hguard Hdomain Hframe Hprovenance Hlookup Hbranch).
  iFrame "Hraw Hcont".
Qed.
Print Assumptions decodeItemStringSuccessorNamed.

#[export] Hint Extern 1 (@ZesuCanonicalAnchor ?Sigma _ _ _) =>
  match goal with
  | Hfold : decodeItemByteFoldFacts ?args ?n ?i ?payloadStart ?lengthBytes,
    Hprovenance : decodeItemFoldProvenance ?args false ?prefix ?rest ?n ?payloadStart ?lengthBytes,
    Hlookup : decodeItemInputBytes ?args !! Z.to_nat (1 + ?i) = Some ?next |- _ =>
      unfold ZesuCanonicalAnchor;
      exact (@decodeItemStringSuccessorNamed Sigma _ _ args prefix rest n i
        payloadStart lengthBytes next)
  end : typeclass_instances.

Lemma decodeItemStringFlagUnitIntroduction `{!islaG Sigma} `{!threadG}
    (b : bv 64) (remaining : isla_trace) :
  Z.land (bv_unsigned b) 131072 = 0 ->
  @ZesuPureFactIntro Sigma
    (∃ _ : unit,
      ⌜Val_Bool (bool_decide (bv_and b 131072 = 0%bv)) = Val_Bool true⌝ ∗
      wp_asm remaining)%I
    (wp_asm remaining).
Proof.
  intros Hflag. unfold ZesuPureFactIntro.
  assert (Hbits : bv_and b 131072 = 0%bv).
  { apply bv_eq. rewrite bv_and_unsigned. change (Z.land (bv_unsigned b) 131072 = 0). exact Hflag. }
  rewrite bool_decide_true; [|exact Hbits].
  iIntros "Hremaining". iExists tt. iFrame. done.
Qed.
Print Assumptions decodeItemStringFlagUnitIntroduction.

#[export] Hint Extern 1 (@ZesuPureFactIntro ?Sigma ?target _) =>
  lazymatch target with
  | @bi_exist _ unit ?body =>
      let value := eval cbv beta zeta delta [LET_ID] in (body tt) in
      let product := lazymatch value with
        | (?left ∗ ?right)%I => constr:(value)
        | ?alias ?argument =>
            let local_alias_check := constr:(ltac:(is_var alias; exact I) : True) in
            let exposed := eval cbv delta [alias] in value in
            eval cbv beta zeta delta [LET_ID] in exposed
        end in
      lazymatch product with
      | (⌜Val_Bool (bool_decide (bv_and ?b 131072 = 0%bv)) = Val_Bool true⌝ ∗ ?rest)%I =>
          let remainder := lazymatch rest with
            | wp_asm ?remaining => constr:(rest)
            | ?alias ?argument =>
                let local_alias_check := constr:(ltac:(is_var alias; exact I) : True) in
                let exposed := eval cbv delta [alias] in rest in
                eval cbv beta zeta delta [LET_ID] in exposed
            end in
          lazymatch remainder with
          | wp_asm ?remaining =>
              match goal with
              | Hflag : Z.land (bv_unsigned ?owned_b) 131072 = 0 |- _ =>
                  unify owned_b b;
                  exact (@decodeItemStringFlagUnitIntroduction Sigma _ _ b remaining Hflag)
              end
          end
      end
  end : typeclass_instances.

