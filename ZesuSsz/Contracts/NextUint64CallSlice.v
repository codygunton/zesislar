From Coq Require Import List ZArith.ZArith Lia.
From stdpp Require Import base list list_numbers bitvector.definitions.
Require Import EvmSailRlp.evm_rlp_types.
Require Import ZesuSsz.Automation2.CallSliceInterface.
Require Import ZesuSsz.Contracts.RlpDecodeItem.
Require Import ZesuSsz.Contracts.RlpDecodeItemContract.
Require Import ZesuSsz.Contracts.DecodeItemCallData.
Require Import ZesuSsz.Contracts.ParentHeaderRootFacts.
Require Import ZesuSsz.Contracts.NextUint64BlockEntries.
Require Import ZesuSsz.Contracts.NextUint64DomainRanges.
Require Import ZesuSsz.Contracts.AbiBytes.
Require ZesuSsz.Contracts.DecodeItemFrameImage.
Require ZesuSsz.Contracts.DecodeItemPayloadBounds.
Require Import ZesuSsz.Interfaces.DecodeItem.
Require Export ZesuSsz.Contracts.DecodeItemCallSlice.
Import ListNotations.
Local Open Scope Z_scope.

(* nextUint64's side of the call-site step (`Automation2/CallSlice.v`). *)
Lemma nextUint64SliceWords (pointer count s : Z) :
  0 <= pointer < 2 ^ 64 -> 0 <= count < 2 ^ 64 ->
  bv_unsigned (Z_to_bv 64 (little_endian_to_bv 8 (take (N.to_nat 8)
     (drop (Z.to_nat (s + 0 - s)) (nextUint64SliceImage pointer count))))) = pointer /\
  bv_unsigned (Z_to_bv 64 (little_endian_to_bv 8 (take (N.to_nat 8)
     (drop (Z.to_nat (s + 8 - s)) (nextUint64SliceImage pointer count))))) = count.
Proof.
  intros Hpointer Hcount.
  replace (s + 0 - s) with 0 by lia. replace (s + 8 - s) with 8 by lia.
  change (Z.to_nat 0) with 0%nat. change (Z.to_nat 8) with 8%nat. change (N.to_nat 8) with 8%nat.
  unfold nextUint64SliceImage. rewrite <- !nextUint64Word64BytesEncoding.
  assert (Hl1 : length (bv_to_little_endian 8 8 pointer) = 8%nat)
    by (rewrite length_bv_to_little_endian; [reflexivity | lia]).
  assert (Hl2 : length (bv_to_little_endian 8 8 count) = 8%nat)
    by (rewrite length_bv_to_little_endian; [reflexivity | lia]).
  rewrite !ZesuSsz.Contracts.DecodeItemPayloadBounds.littleEndianBv.
  split.
  - cbn [drop].
    rewrite firstn_app, Hl1, Nat.sub_diag, firstn_O, app_nil_r, firstn_all2; [|rewrite Hl1; constructor].
    rewrite (ZesuSsz.Contracts.DecodeItemFrameImage.littleEndian_machine_bytes 8); [|exact Hpointer].
    rewrite Z_to_bv_unsigned. apply bv_wrap_small. exact Hpointer.
  - rewrite drop_app_length'; [|exact Hl1].
    rewrite firstn_all2; [|rewrite Hl2; constructor].
    rewrite (ZesuSsz.Contracts.DecodeItemFrameImage.littleEndian_machine_bytes 8); [|exact Hcount].
    rewrite Z_to_bv_unsigned. apply bv_wrap_small. exact Hcount.
Qed.

Lemma nextUint64SliceWindow (params : NextUint64Args) :
  nextUint64BoundaryDomain params ->
  nextInputPointer (nextUint64Base params) <=
    bv_unsigned (Z_to_bv 64 (little_endian_to_bv 8 (take (N.to_nat 8)
      (drop (Z.to_nat (nextSlicePointer (nextUint64Base params) + 0 - nextSlicePointer (nextUint64Base params)))
        (nextUint64SliceImage (nextInputPointer (nextUint64Base params))
           (Z.of_nat (length (nextInputBytes (nextUint64Base params))))))))) /\
  bv_unsigned (Z_to_bv 64 (little_endian_to_bv 8 (take (N.to_nat 8)
      (drop (Z.to_nat (nextSlicePointer (nextUint64Base params) + 0 - nextSlicePointer (nextUint64Base params)))
        (nextUint64SliceImage (nextInputPointer (nextUint64Base params))
           (Z.of_nat (length (nextInputBytes (nextUint64Base params)))))))))
  + bv_unsigned (Z_to_bv 64 (little_endian_to_bv 8 (take (N.to_nat 8)
      (drop (Z.to_nat (nextSlicePointer (nextUint64Base params) + 8 - nextSlicePointer (nextUint64Base params)))
        (nextUint64SliceImage (nextInputPointer (nextUint64Base params))
           (Z.of_nat (length (nextInputBytes (nextUint64Base params)))))))))
  <= nextInputPointer (nextUint64Base params) + Z.of_nat (length (nextInputBytes (nextUint64Base params))).
Proof.
  intros Hd. pose proof (nextUint64BoundaryDomainRanges params Hd) as (_ & Hp & Hl & _).
  change (bv_modulus 64) with (2 ^ 64) in *.
  destruct (nextUint64SliceWords (nextInputPointer (nextUint64Base params))
    (Z.of_nat (length (nextInputBytes (nextUint64Base params))))
    (nextSlicePointer (nextUint64Base params)) Hp Hl) as [-> ->].
  lia.
Qed.

(* nextUint64 may call decodeItem on any window of its input with any 40-byte
   output slot of its own 96-byte frame. *)
Lemma nextUint64DecodeItemCallDomain (params : NextUint64Args) (p l out sp : bv 64) (k ie : Z)
    (rest : list (bv 64)) (before : list byte) :
  nextUint64BoundaryDomain params ->
  (nextInputPointer (nextUint64Base params) <= bv_unsigned p /\
   bv_unsigned p + bv_unsigned l <= nextInputPointer (nextUint64Base params) +
     Z.of_nat (length (nextInputBytes (nextUint64Base params)))) ->
  bv_unsigned sp = nextStackPointer (nextUint64Base params) - 96 ->
  bv_unsigned out = nextStackPointer (nextUint64Base params) - 96 + k ->
  0 <= k <= 56 ->
  ie = nextUint64InputEnd params ->
  length before = 40%nat ->
  decodeItemCallDomain (decodeItemCallDataArgs (out :: p :: l :: rest) sp ie
    (take (Z.to_nat (bv_unsigned l))
       (drop (Z.to_nat (bv_unsigned p - nextInputPointer (nextUint64Base params)))
          (nextInputBytes (nextUint64Base params)))) before).
Proof.
  intros Hd [Hlo Hhi] Hsp Hout Hk Hie Hbefore.
  apply decodeItemCallDomainIntro.
  unfold decodeItemC1BDomain, decodeItemArgsWellFormed, decodeItemEntryLayout, separateRanges, decodeItemCallDataArgs.
  cbn.
  unfold nextUint64BoundaryDomain, nextUint64EntryLayout, decodeItemEntryLayout, separateRanges in Hd.
  cbv zeta in Hd. cbn in Hd.
  rewrite length_take, length_drop, Hsp, Hout, Hie.
  pose proof (bv_unsigned_in_range _ l) as Hl.
  pose proof (bv_unsigned_in_range _ p) as Hp.
  change (bv_modulus 64) with 18446744073709551616 in *.
  change (2 ^ 64) with 18446744073709551616 in *.
  repeat match goal with H : _ /\ _ |- _ => destruct H end.
  repeat match goal with H : (_ | _) |- _ => clear H end.
  (* [length] is counted at [byte] in the domain and at [bv 8] after
     [length_take]/[length_drop]; lia sees two atoms. One spelling first. *)
  repeat match goal with
  | H : context [@length ?T ?x] |- _ =>
      lazymatch T with bv 8 => fail | _ => idtac end;
      change (@length T x) with (@length (bv 8) x) in H
  end;
  repeat match goal with
  | |- context [@length ?T ?x] =>
      lazymatch T with bv 8 => fail | _ => idtac end;
      change (@length T x) with (@length (bv 8) x)
  end.
  repeat split; lia.
Qed.

#[export] Instance nextUint64DecodeItemCallSlice :
  ZesuCallSliceCaller nextUint64BoundaryDomain decodeItemCallSliceInterface
    (fun params => nextInputPointer (nextUint64Base params))
    (fun params => nextInputBytes (nextUint64Base params))
    (fun params => nextStackPointer (nextUint64Base params) - 96)
    (fun params => nextUint64InputEnd params)
    56.
Proof.
  intros params p l out sp k ie rest before Hd Hwin Hsp Hout Hk Hie Hbefore.
  exact (nextUint64DecodeItemCallDomain params p l out sp k ie rest before
    Hd Hwin Hsp Hout Hk Hie Hbefore).
Qed.

(* nextUint64's input is the whole slice its slice argument names. *)
#[export] Instance nextUint64DecodeItemCallWindow :
  ZesuCallSliceCallerWindow nextUint64BoundaryDomain (fun params =>
  nextInputPointer (nextUint64Base params) <=
    bv_unsigned (Z_to_bv 64 (little_endian_to_bv 8 (take (N.to_nat 8)
      (drop (Z.to_nat (nextSlicePointer (nextUint64Base params) + 0 - nextSlicePointer (nextUint64Base params)))
        (nextUint64SliceImage (nextInputPointer (nextUint64Base params))
           (Z.of_nat (length (nextInputBytes (nextUint64Base params))))))))) /\
  bv_unsigned (Z_to_bv 64 (little_endian_to_bv 8 (take (N.to_nat 8)
      (drop (Z.to_nat (nextSlicePointer (nextUint64Base params) + 0 - nextSlicePointer (nextUint64Base params)))
        (nextUint64SliceImage (nextInputPointer (nextUint64Base params))
           (Z.of_nat (length (nextInputBytes (nextUint64Base params)))))))))
  + bv_unsigned (Z_to_bv 64 (little_endian_to_bv 8 (take (N.to_nat 8)
      (drop (Z.to_nat (nextSlicePointer (nextUint64Base params) + 8 - nextSlicePointer (nextUint64Base params)))
        (nextUint64SliceImage (nextInputPointer (nextUint64Base params))
           (Z.of_nat (length (nextInputBytes (nextUint64Base params)))))))))
  <= nextInputPointer (nextUint64Base params) + Z.of_nat (length (nextInputBytes (nextUint64Base params)))) :=
  nextUint64SliceWindow.

