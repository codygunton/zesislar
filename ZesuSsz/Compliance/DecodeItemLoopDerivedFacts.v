From Coq Require Import List ZArith Lia.
Require Import isla.riscv64.riscv64.
Require Import ZesuMachineMap.Machine.
Require Import ZesuSsz.Contracts.RlpDecodeItemByteFold.
Require Import ZesuSsz.Contracts.RlpDecodeItemContract.
Require Import ZesuSsz.Automation.PureFacts.
Require Import ZesuSsz.Automation.BitvectorFacts.
Require Import ZesuSsz.Compliance.DecodeItemCorrectedWitnessSelections.
Require Import ZesuSsz.Compliance.DecodeItemFoldExitFacts.
Require Import ZesuSsz.Contracts.IslarisCode.
Require Import ZesuSsz.Contracts.RlpDecodeItem.
Require Import ZesuSsz.Proofs.DecodeItem.ByteFoldPure.
Open Scope Z_scope.

#[export] Instance decodeItemFoldDerived args n i ps bytes :
  ZesuDerivedFacts (decodeItemByteFoldFacts args n i ps bytes)
    ((Z_to_bv 64 (ps+i) + 1)%bv = Z_to_bv 64 (ps+(i+1)) /\
     Z.of_nat (length bytes) = n /\
     (forall next, i<n ->
       decodeItemInputBytes args !! Z.to_nat (1+i) = Some next ->
       nth_error bytes (Z.to_nat i) = Some next) /\
     (forall next, i<n ->
       decodeItemInputBytes args !! Z.to_nat (1+i) = Some next ->
       bv_or (Z_to_bv 64 (bigEndian (firstn (Z.to_nat i) bytes)) ≪ 8)
         (bv_zero_extend 64 next) = Z_to_bv 64 (bigEndian (firstn (Z.to_nat (i+1)) bytes))) /\
     (forall next, i<n ->
       decodeItemInputBytes args !! Z.to_nat (1+i) = Some next ->
       decodeItemByteFoldFacts args n (i+1) ps bytes) /\
     (decodeItemC1BDomain args -> i<n ->
       (Z_to_bv 64 (ps+i) + Z_to_bv 64 1)%bv <> Z_to_bv 64 (ps+n) -> i+1<n) /\
     (i<n -> 0<=decodeItemInputPointer args ->
       decodeItemInputPointer args + decodeItemInputLength args < word64Modulus ->
       (Z_to_bv 64 (ps+i) + 1)%bv = Z_to_bv 64 (ps+n) -> i+1=n) /\
     (forall next, i<n -> 0<=decodeItemInputPointer args ->
       decodeItemInputPointer args + decodeItemInputLength args < word64Modulus ->
       (Z_to_bv 64 (ps+i) + 1)%bv = Z_to_bv 64 (ps+n) ->
       decodeItemInputBytes args !! Z.to_nat (1+i) = Some next ->
       bv_or (Z_to_bv 64 (bigEndian (firstn (Z.to_nat i) bytes)) ≪ 8)
         (bv_zero_extend 64 next) = Z_to_bv 64 (bigEndian (firstn (Z.to_nat n) bytes))) /\
     (forall next, i<n -> 0<=decodeItemInputPointer args ->
       decodeItemInputPointer args + decodeItemInputLength args < word64Modulus ->
       (Z_to_bv 64 (ps+i) + 1)%bv = Z_to_bv 64 (ps+n) ->
       decodeItemInputBytes args !! Z.to_nat (1+i) = Some next ->
       decodeItemByteFoldFacts args n n ps bytes)).
Proof.
  unfold ZesuDerivedFacts. intro Hfold.
  split; first exact (decodeItemFoldSteppedCursor args n i ps bytes Hfold).
  split; first exact (proj1 (proj2 (proj2 (proj2 (proj2 Hfold))))).
  split.
  - intros next Hguard Hnth. rewrite -decodeItemListLookupNthError in Hnth.
    exact (decodeItemFoldByteAtSuccessor args n i ps bytes next Hfold Hguard Hnth).
  - split.
    + intros next Hguard Hnth. rewrite -decodeItemListLookupNthError in Hnth.
      exact (decodeItemFoldSteppedAccumulator args n i ps bytes next Hfold Hguard Hnth).
    + split.
      * intros next Hguard Hnth. rewrite -decodeItemListLookupNthError in Hnth.
        pose proof (decodeItemFoldByteAtSuccessor args n i ps bytes next Hfold Hguard Hnth) as Hbyte.
        exact (proj1 (decodeItem_fold_preservation args n i ps bytes next Hfold Hguard Hbyte)).
      * split.
        -- intros Hdomain Hguard Hbranch.
           exact (proj1 (decodeItemByteFoldBackedgeGuard args n i ps bytes Hdomain Hfold Hguard Hbranch)).
        -- split.
           ++ exact (decodeItemFoldExitIndex args n i ps bytes Hfold).
           ++ split.
              ** intros next. exact (decodeItemFoldExitAccumulator args n i ps bytes next Hfold).
              ** intros next Hguard Hptr Hend Hbranch Hnth.
                 pose proof (decodeItemFoldExitIndex args n i ps bytes Hfold Hguard Hptr Hend Hbranch) as Hindex.
                 rewrite -decodeItemListLookupNthError in Hnth.
                 pose proof (decodeItemFoldByteAtSuccessor args n i ps bytes next Hfold Hguard Hnth) as Hbyte.
                 pose proof (proj1 (decodeItem_fold_preservation args n i ps bytes next Hfold Hguard Hbyte)) as Hstep.
                 rewrite Hindex in Hstep. exact Hstep.
Qed.

#[export] Instance decodeItemFoldFaultDerived args :
  ZesuDerivedFacts (decodeItemDomainAt (decodeItemReturnAddress args) decodeItemC1BDomain args)
    (forall (n i ps : Z) (bytes : list byte),
      decodeItemByteFoldFacts args n i ps bytes -> i<n ->
      bv_signed (bv_zero_extend 128 ((Z_to_bv 64 (ps+i) + 0)%bv)) < 2684354560 ->
      ~ (bv_signed (bv_zero_extend 128 ((Z_to_bv 64 (ps+i) + 0)%bv) + 1)%bv <=
          bv_signed (2147483648%bv : bv 128)) ->
      ~ (bv_signed (bv_zero_extend 128 ((Z_to_bv 64 (ps+i) + 0)%bv) + 1)%bv <=
          bv_signed (2148632184%bv : bv 128)) -> False).
Proof.
 unfold ZesuDerivedFacts. intros Hd n i ps bytes Hf Hg Hlow Hram Hinput.
 destruct Hf as (Hn & Hi & Hps & Hbytes & Hlength & Hfit).
 destruct Hd as (_ & Hlen & Hstorage & Hlayout).
 unfold decodeItemEntryLayout in Hlayout.
 destruct Hlayout as (Hp & Hl & Hnowrap & Ho & Hon & Hsp & Hsl & Hsu & Hsep1 & Hsep2 & Hsep3 & Hret & Halign & Hreadable & Hrest).
 assert (Hcursor : (0 <= ps + i < bv_modulus 64)%Z) by
   (unfold RlpDecodeItem.word64Modulus, bv_modulus in *; lia).
 assert (HnextFit : (ps + i + 1 <= decodeItemInputPointer args + decodeItemInputLength args)%Z) by lia.
 assert (Hword : ((Z_to_bv 64 (ps + i)%Z + 0)%bv) = Z_to_bv 64 (ps + i)%Z) by bv_solve.
 rewrite Hword in Hlow, Hram, Hinput.
 rewrite zesu_signed_zero_extend_64_128 in Hlow.
 assert (Hwide : bv_signed (bv_zero_extend 128 (Z_to_bv 64 (ps + i)%Z) + 1)%bv =
   (bv_unsigned (Z_to_bv 64 (ps + i)%Z) + 1)%Z) by
   (apply zesu_signed_zero_extend_add_64_128; bv_solve).
 rewrite Hwide in Hram, Hinput.
 rewrite (Z_to_bv_small 64 _ Hcursor) in Hlow, Hram, Hinput.
 change (~ (ps + i + 1 <= 2147483648))%Z in Hram.
 change (~ (ps + i + 1 <= 2148632184))%Z in Hinput.
 destruct Hreadable as [[Hlower Hupper]|[Hlower Hupper]];
 cbn [mapInputBufferAddress mapInputCapacity mapRamBase machineRamEnd mapRamSize defaultMap] in Hlower, Hupper;
 lia.
Qed.
