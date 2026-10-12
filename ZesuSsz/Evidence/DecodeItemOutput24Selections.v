Require Import ZesuSsz.Automation.All.
Require Import ZesuSsz.Automation.Approved.
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Contracts.RlpDecodeItem.
Require Import ZesuSsz.Contracts.RlpDecodeItemContract.
Require Import ZesuSsz.Contracts.DecodeItemReturnFacts.
Require Import ZesuSsz.Contracts.RlpDecodeItemBlockEntries.
From Coq Require Import List ZArith NArith Lia.
Open Scope Z_scope.

(* These pure facts describe a candidate. They do not select a spatial resource. *)
Definition decodeItemOutput24Selection (args : DecodeItemArgs)
    (storage : list byte) : Prop :=
  let address := bv_unsigned
    (bv_add (Z_to_bv 64 (decodeItemOutputPointer args)) (24%bv : bv 64)) in
  address = decodeItemOutputPointer args + 24 /\
  Z.of_nat 24 = address - decodeItemOutputPointer args /\
  (address - decodeItemOutputPointer args) mod 8 = 0 /\
  Z.of_nat 3 = (address - decodeItemOutputPointer args) / 8 /\
  (24 + N.to_nat 8 <= List.length storage)%nat /\
  match MKArray 8 (decodeItemOutputPointer args) storage with
  | MKArray width base _ =>
      width = 8%N /\ base = decodeItemOutputPointer args /\
      (width =? 64)%N = false
  | _ => False
  end.

Lemma decodeItemOutput24SelectionFacts (args : DecodeItemArgs)
    (storage : list byte) :
  List.length storage = 40%nat ->
  0 <= decodeItemOutputPointer args ->
  decodeItemOutputPointer args + 40 < RlpDecodeItem.word64Modulus ->
  decodeItemOutput24Selection args storage.
Proof.
  intros Hlength Hlower Hupper.
  unfold decodeItemOutput24Selection.
  assert (Hbounds : 0 <= decodeItemOutputPointer args + 24 < bv_modulus 64).
  { unfold RlpDecodeItem.word64Modulus in Hupper. unfold bv_modulus. cbn. lia. }
  replace (bv_add (Z_to_bv 64 (decodeItemOutputPointer args)) (24%bv : bv 64))
    with (Z_to_bv 64 (decodeItemOutputPointer args + 24)) by bv_solve.
  rewrite (Z_to_bv_small 64 _ Hbounds).
  replace (decodeItemOutputPointer args + 24 - decodeItemOutputPointer args) with 24 by lia.
  rewrite Hlength. cbn. repeat split; lia.
Qed.

Lemma decodeItemReturnEntryOutput24Selection `{!islaG Sigma} `{!threadG}
    (args : DecodeItemArgs) (locals : DecodeItemReturnLocals) :
  decodeItemReturnEntryCore args locals ⊢
    ⌜decodeItemOutput24Selection args (returnStorage locals)⌝.
Proof.
  iIntros "Hentry".
  iEval (unfold decodeItemReturnEntryCore) in "Hentry".
  iDestruct "Hentry" as "(_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & %Hfacts & _)".
  destruct Hfacts as [Hdomain [Hframe Hlength]].
  iPureIntro. apply decodeItemOutput24SelectionFacts; [exact Hlength | |].
  all: unfold decodeItemDomainAt, decodeItemC1BDomain,
    decodeItemArgsWellFormed, RlpDecodeItem.decodeItemEntryLayout in Hdomain;
    naive_solver.
Qed.

Lemma decodeItemEntry6a40Output24Selection `{!islaG Sigma} `{!threadG}
    (args : DecodeItemArgs) (locals : DecodeItemReturnLocals)
    (inputPrefix : byte) (rest : list byte) (headerLength payloadLength : Z) :
  decodeItemEntryAt800d6a40 args locals inputPrefix rest headerLength payloadLength ⊢
    ⌜decodeItemOutput24Selection args (returnStorage locals)⌝.
Proof.
  iIntros "Hentry".
  iEval (unfold decodeItemEntryAt800d6a40) in "Hentry".
  iDestruct "Hentry" as "[Hcore _]".
  iApply decodeItemReturnEntryOutput24Selection. iExact "Hcore".
Qed.

Lemma decodeItemEntry6a78Output24Selection `{!islaG Sigma} `{!threadG}
    (args : DecodeItemArgs) (locals : DecodeItemReturnLocals)
    (inputPrefix : byte) (rest : list byte)  :
  decodeItemEntryAt800d6a78 args locals inputPrefix rest ⊢
    ⌜decodeItemOutput24Selection args (returnStorage locals)⌝.
Proof.
  iIntros "Hentry".
  iEval (unfold decodeItemEntryAt800d6a78) in "Hentry".
  iDestruct "Hentry" as "[Hcore _]".
  iApply decodeItemReturnEntryOutput24Selection. iExact "Hcore".
Qed.

Lemma decodeItemEntry69b0Output24Selection `{!islaG Sigma} `{!threadG}
    (args : DecodeItemArgs) (locals : DecodeItemReturnLocals)
    (inputPrefix : byte) (rest : list byte)  :
  decodeItemEntryAt800d69b0 args locals inputPrefix rest ⊢
    ⌜decodeItemOutput24Selection args (returnStorage locals)⌝.
Proof.
  iIntros "Hentry".
  iEval (unfold decodeItemEntryAt800d69b0) in "Hentry".
  iDestruct "Hentry" as "[Hcore _]".
  iApply decodeItemReturnEntryOutput24Selection. iExact "Hcore".
Qed.

(* S151 retains this complete image. The other images have printing gaps. *)
Lemma decodeItemOutput24UpdatedExtent (before head : list byte)
    (a b value : byte) :
  List.length before = 40%nat -> List.length head = 16%nat ->
  (24 + N.to_nat 8 <= List.length
    (head ++ <[0%nat:=value]>
      (drop 8 (drop 8 (take 32 before ++ a :: b :: drop 34 before)))))%nat.
Proof.
  intros Hbefore Hhead.
  rewrite length_app length_insert !length_drop length_app length_take.
  simpl. rewrite length_drop Hbefore Hhead. simpl. lia.
Qed.
