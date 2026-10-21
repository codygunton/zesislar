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

Lemma decodeItemFoldTerminalAccumulatorTransport args (n i ps : Z) bytes next :
 decodeItemByteFoldFacts args n i ps bytes -> i<n ->
 decodeItemInputBytes args !! Z.to_nat (1+i) = Some next ->
 i+1=n ->
 bv_or (Z_to_bv 64 (bigEndian (firstn (Z.to_nat i) bytes)) ≪ 8)
   (bv_zero_extend 64 next) = Z_to_bv 64 (bigEndian (firstn (Z.to_nat n) bytes)).
Proof.
 intros Hfold Hguard Hlookup Hindex.
 rewrite -decodeItemListLookupNthError in Hlookup.
 pose proof (decodeItemFoldSteppedAccumulator args n i ps bytes next Hfold Hguard Hlookup) as Hstep.
 rewrite Hindex in Hstep. exact Hstep.
Qed.

#[export] Hint Extern 1
  (SimplAnd (bv_or (Z_to_bv 64 (bigEndian (firstn (Z.to_nat ?i) ?bytes)) ≪ 8)
    (bv_zero_extend 64 ?next) = Z_to_bv 64 (bigEndian (firstn (Z.to_nat ?n) ?bytes))) True) =>
  match goal with
  | Hfold : decodeItemByteFoldFacts ?args n i ?ps bytes,
    Hguard : i<n,
    Hlookup : decodeItemInputBytes ?args !! Z.to_nat (1+i) = Some next |- _ =>
    unfold SimplAnd; split;
    [intros _; eapply (decodeItemFoldTerminalAccumulatorTransport args n i ps bytes next);
     [exact Hfold | exact Hguard | exact Hlookup |
      first [assumption | eapply (decodeItemFoldExitIndex args n i ps bytes); eassumption]]
    | intros _; exact I]
  end : typeclass_instances.


Lemma decodeItemFoldCursorSeparate args (n i ps : Z) (bytes : list byte) :
  ZesuDerivedFacts (decodeItemByteFoldFacts args n i ps bytes)
    ((Z_to_bv 64 (ps+i)+1)%bv = Z_to_bv 64 (ps+(i+1))).
Proof.
  exact (decodeItemFoldSteppedCursor args n i ps bytes).
Qed.

Lemma decodeItemFoldByteSeparate args (n i ps : Z) (bytes : list byte) :
  ZesuDerivedFacts (decodeItemByteFoldFacts args n i ps bytes)
    (forall next : bv 8, i<n -> decodeItemInputBytes args !! Z.to_nat (1+i) = Some next -> nth_error bytes (Z.to_nat i) = Some next).
Proof.
  intros Hfold next Hguard Hlookup.
  rewrite -decodeItemListLookupNthError in Hlookup.
  exact (decodeItemFoldByteAtSuccessor args n i ps bytes next Hfold Hguard Hlookup).
Qed.

Lemma decodeItemFoldSuccessorAccumulatorSeparate args (n i ps : Z) (bytes : list byte) :
  ZesuDerivedFacts (decodeItemByteFoldFacts args n i ps bytes)
    (forall next : bv 8, i<n -> decodeItemInputBytes args !! Z.to_nat (1+i) = Some next -> bv_or (Z_to_bv 64 (bigEndian (firstn (Z.to_nat i) bytes)) ≪ 8) (bv_zero_extend 64 next) = Z_to_bv 64 (bigEndian (firstn (Z.to_nat (i+1)) bytes))).
Proof.
  intros Hfold next Hguard Hlookup.
  rewrite -decodeItemListLookupNthError in Hlookup.
  exact (decodeItemFoldSteppedAccumulator args n i ps bytes next Hfold Hguard Hlookup).
Qed.

Lemma decodeItemFoldSuccessorFoldSeparate args (n i ps : Z) (bytes : list byte) :
  ZesuDerivedFacts (decodeItemByteFoldFacts args n i ps bytes)
    (forall next : bv 8, i<n -> decodeItemInputBytes args !! Z.to_nat (1+i) = Some next -> decodeItemByteFoldFacts args n (i+1) ps bytes).
Proof.
  intros Hfold next Hguard Hlookup.
  rewrite -decodeItemListLookupNthError in Hlookup.
  pose proof (decodeItemFoldByteAtSuccessor args n i ps bytes next Hfold Hguard Hlookup) as Hbyte.
  exact (proj1 (decodeItem_fold_preservation args n i ps bytes next Hfold Hguard Hbyte)).
Qed.

Lemma decodeItemFoldBackedgeGuardSeparate args (n i ps : Z) (bytes : list byte) :
  ZesuDerivedFacts (decodeItemByteFoldFacts args n i ps bytes)
    (decodeItemDomainAt (decodeItemReturnAddress args) decodeItemC1BDomain args -> i<n -> (Z_to_bv 64 (ps+i)+1)%bv <> Z_to_bv 64 (ps+n) -> i+1<n).
Proof.
  unfold ZesuDerivedFacts. intro Hfold.
  intros Hdomain Hguard Hbranch.
  exact (proj1 (decodeItemByteFoldBackedgeGuard args n i ps bytes (proj2 Hdomain) Hfold Hguard Hbranch)).
Qed.

Lemma decodeItemFoldTerminalIndexSeparate args (n i ps : Z) (bytes : list byte) :
  ZesuDerivedFacts (decodeItemByteFoldFacts args n i ps bytes)
    (i<n -> 0<=decodeItemInputPointer args -> decodeItemInputPointer args + decodeItemInputLength args < word64Modulus -> (Z_to_bv 64 (ps+i)+1)%bv = Z_to_bv 64 (ps+n) -> i+1=n).
Proof.
  exact (decodeItemFoldExitIndex args n i ps bytes).
Qed.

Lemma decodeItemFoldTerminalAccumulatorSeparate args (n i ps : Z) (bytes : list byte) :
  ZesuDerivedFacts (decodeItemByteFoldFacts args n i ps bytes)
    (forall next : bv 8, i<n -> 0<=decodeItemInputPointer args -> decodeItemInputPointer args + decodeItemInputLength args < word64Modulus -> (Z_to_bv 64 (ps+i)+1)%bv = Z_to_bv 64 (ps+n) -> decodeItemInputBytes args !! Z.to_nat (1+i) = Some next -> bv_or (Z_to_bv 64 (bigEndian (firstn (Z.to_nat i) bytes)) ≪ 8) (bv_zero_extend 64 next) = Z_to_bv 64 (bigEndian (firstn (Z.to_nat n) bytes))).
Proof.
  intro Hfold. intros next.
  exact (decodeItemFoldExitAccumulator args n i ps bytes next Hfold).
Qed.

Lemma decodeItemFoldTerminalFoldSeparate args (n i ps : Z) (bytes : list byte) :
  ZesuDerivedFacts (decodeItemByteFoldFacts args n i ps bytes)
    (forall next : bv 8, i<n -> 0<=decodeItemInputPointer args -> decodeItemInputPointer args + decodeItemInputLength args < word64Modulus -> (Z_to_bv 64 (ps+i)+1)%bv = Z_to_bv 64 (ps+n) -> decodeItemInputBytes args !! Z.to_nat (1+i) = Some next -> decodeItemByteFoldFacts args n n ps bytes).
Proof.
  intros Hfold next Hguard Hptr Hend Hbranch Hlookup.
  pose proof (decodeItemFoldExitIndex args n i ps bytes Hfold Hguard Hptr Hend Hbranch) as Hindex.
  rewrite -decodeItemListLookupNthError in Hlookup.
  pose proof (decodeItemFoldByteAtSuccessor args n i ps bytes next Hfold Hguard Hlookup) as Hbyte.
  pose proof (proj1 (decodeItem_fold_preservation args n i ps bytes next Hfold Hguard Hbyte)) as Hstep.
  rewrite Hindex in Hstep. exact Hstep.
Qed.

(* Inspect the declared output so the duplicate guard and consumer agree. *)
Ltac decodeItem_loop_derived_if_new instance :=
  lazymatch type of instance with
  | ZesuDerivedFacts _ ?derived =>
    lazymatch goal with
    | _ : derived |- _ => fail
    | _ => exact instance
    end
  end.

(* Each successful query adds one fact that is absent from the context. *)
#[export] Hint Extern 1
  (ZesuDerivedFacts (decodeItemByteFoldFacts ?args ?n ?i ?ps ?bytes) _) =>
  first [
    let instance := constr:(decodeItemFoldCursorSeparate args n i ps bytes) in
      decodeItem_loop_derived_if_new instance
  | let instance := constr:(decodeItemFoldByteSeparate args n i ps bytes) in
      decodeItem_loop_derived_if_new instance
  | let instance := constr:(decodeItemFoldSuccessorAccumulatorSeparate args n i ps bytes) in
      decodeItem_loop_derived_if_new instance
  | let instance := constr:(decodeItemFoldSuccessorFoldSeparate args n i ps bytes) in
      decodeItem_loop_derived_if_new instance
  | let instance := constr:(decodeItemFoldBackedgeGuardSeparate args n i ps bytes) in
      decodeItem_loop_derived_if_new instance
  | let instance := constr:(decodeItemFoldTerminalIndexSeparate args n i ps bytes) in
      decodeItem_loop_derived_if_new instance
  | let instance := constr:(decodeItemFoldTerminalAccumulatorSeparate args n i ps bytes) in
      decodeItem_loop_derived_if_new instance
  | let instance := constr:(decodeItemFoldTerminalFoldSeparate args n i ps bytes) in
      decodeItem_loop_derived_if_new instance
  ] : typeclass_instances.
