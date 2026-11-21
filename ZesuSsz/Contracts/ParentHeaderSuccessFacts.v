(* Step 2.4 M1, the pure pieces of decodeParentHeader's success exits.
   Owner: contract fact (pure lemmas over contract predicates; no Iris, no
   automation umbrella).

   1. The inline integer fields 9 to 11 are folded by the loops at 0x02d0,
      0x0334 and 0x039c (accumulators x21, x22, x20). The loop classes must
      carry the fold invariant
        bv_unsigned acc = zesu_byte_window_fold (parentHeaderInputBytes args)
          (Z.to_nat (bv_unsigned start - bv_unsigned (parentHeaderInputPointer args)))
          (Z.to_nat i)
      (start = the payload pointer the loop starts from, i = the loop index);
      [parentHeaderFoldStart], [parentHeaderFoldStep] and [parentHeaderFoldExit]
      are its entry, back-edge and exit, the last in the value spelling of
      [candidateWalkIntegerStep]. The text the generator lane declares is in
      _build/agents/rebuild/2.4m1/LOOP_FACTS.md.
   2. The success terminal over an explicit byte list: the result bytes the
      return block stores (three words, three 16-byte option records, the
      zero tag half-word, six bytes the contract leaves free) satisfy
      [parentHeaderCandidateResult] when the candidate succeeds with those
      values ([parentHeaderSuccessResult]). *)
From Coq Require Import List ZArith Lia.
From stdpp Require Import base list numbers bitvector.definitions.
Require Import EvmSailRlp.evm_rlp_types.
Require Import ZesuSsz.Automation2.ByteWindowFold.
Require Import ZesuSsz.Automation2.ByteWindowFoldWord.
Require Import ZesuSsz.Contracts.RlpDecodeItem.
Require Import ZesuSsz.Contracts.ParentHeader.
Require Import ZesuSsz.Contracts.ParentHeaderRootFacts.
Require Import ZesuSsz.Contracts.Candidates.ParentHeaderCandidate.
Require Import ZesuSsz.Contracts.ParentHeaderCandidateWalk.

Import ListNotations.
Open Scope Z_scope.

(* ---- 1. The integer-field fold loops ---- *)

Lemma parentHeaderFoldStart (bytes : list byte) (start : nat) :
  bv_unsigned (BV 64 0) = zesu_byte_window_fold bytes start (Z.to_nat 0).
Proof. reflexivity. Qed.

(* One iteration: lbu, slli 8, or. At most 8 bytes, so nothing wraps. *)
Lemma parentHeaderFoldStep (bytes : list byte) (start : nat) (i : Z) (acc : bv 64) (b : byte) :
  0 <= i < 8 ->
  bv_unsigned acc = zesu_byte_window_fold bytes start (Z.to_nat i) ->
  nth_error bytes (start + Z.to_nat i)%nat = Some b ->
  bv_unsigned (bv_or (bv_shiftl acc (BV 64 8)) (bv_zero_extend 64 b)) =
    zesu_byte_window_fold bytes start (Z.to_nat (i + 1)).
Proof.
  intros Hi Hacc Hb.
  replace acc with (Z_to_bv 64 (zesu_byte_window_fold bytes start (Z.to_nat i)))
    by (rewrite <- Hacc; apply Z_to_bv_bv_unsigned).
  replace (Z.to_nat (i + 1)) with (S (Z.to_nat i)) by lia.
  apply zesu_byte_window_unsigned_step; [lia | exact Hb].
Qed.

(* Exit (i = payload length): the accumulator is the value the walk appends
   for the field, in the spelling of [candidateWalkIntegerStep]: the payload
   [start, start + len) read inside the call's window [p, p + remaining). *)
Lemma parentHeaderFoldExit (bytes : list byte) (base p start : Z) (remaining len : Z) (acc : bv 64) :
  base <= p <= start -> 0 <= len -> start - p + len <= remaining ->
  bv_unsigned acc = zesu_byte_window_fold bytes (Z.to_nat (start - base)) (Z.to_nat len) ->
  bv_unsigned acc = bigEndian (take (Z.to_nat len)
    (drop (Z.to_nat (start - p)) (take (Z.to_nat remaining) (drop (Z.to_nat (p - base)) bytes)))).
Proof.
  intros Hp Hl Hw ->. unfold zesu_byte_window_fold, zesu_big_endian8, bigEndian. f_equal.
  rewrite skipn_firstn_comm, skipn_skipn, firstn_firstn.
  replace (Z.to_nat (start - p) + Z.to_nat (p - base))%nat with (Z.to_nat (start - base)) by lia.
  f_equal. lia.
Qed.

(* ---- 2. The success terminal ---- *)

(* A 64-bit register stored little-endian (sd), in the spelling of the
   return package's stored bytes. *)
Definition parentHeaderWordBytes (w : bv 64) : list byte :=
  [bv_extract 0 8 w; bv_extract 8 8 w; bv_extract 16 8 w; bv_extract 24 8 w;
   bv_extract 32 8 w; bv_extract 40 8 w; bv_extract 48 8 w; bv_extract 56 8 w].

Lemma parentHeaderWordBytesLength w : length (parentHeaderWordBytes w) = 8%nat.
Proof. reflexivity. Qed.

Lemma byteDigit (n : Z) (k : Z) :
  0 <= k -> bv_unsigned (Z_to_bv 8 ((n / 2 ^ k) mod 256)) = (n / 2 ^ k) mod 256.
Proof.
  intros Hk. apply Z_to_bv_small. unfold bv_modulus. cbn. apply Z.mod_pos_bound. lia.
Qed.

Lemma parentHeaderWordBytesValue (w : bv 64) :
  littleEndian (parentHeaderWordBytes w) = bv_unsigned w.
Proof.
  unfold parentHeaderWordBytes. cbn [littleEndian].
  rewrite !bv_extract_unsigned. unfold bv_wrap, bv_modulus. cbn [Z.of_N].
  rewrite !Z.shiftr_div_pow2 by lia. change (2 ^ 8) with 256.
  pose proof (bv_unsigned_in_range _ w) as Hw. unfold bv_modulus in Hw.
  change (2 ^ Z.of_N 64) with (2 ^ 64) in Hw.
  set (n := bv_unsigned w) in *. clearbody n.
  assert (Hm : forall m, m = m mod 256 + 256 * (m / 256)).
  { intros m. pose proof (Z.div_mod m 256 ltac:(lia)). lia. }
  assert (H64 : n / 2 ^ 64 = 0) by (apply Z.div_small; lia).
  change (n / 2 ^ 0) with (n / 1). rewrite Z.div_1_r.
  replace (n / 2 ^ 16) with ((n / 256) / 256) by (rewrite Z.div_div by lia; reflexivity).
  replace (n / 2 ^ 24) with (((n / 256) / 256) / 256) by (rewrite !Z.div_div by lia; reflexivity).
  replace (n / 2 ^ 32) with ((((n / 256) / 256) / 256) / 256)
    by (rewrite !Z.div_div by lia; reflexivity).
  replace (n / 2 ^ 40) with (((((n / 256) / 256) / 256) / 256) / 256)
    by (rewrite !Z.div_div by lia; reflexivity).
  replace (n / 2 ^ 48) with ((((((n / 256) / 256) / 256) / 256) / 256) / 256)
    by (rewrite !Z.div_div by lia; reflexivity).
  replace (n / 2 ^ 56) with (((((((n / 256) / 256) / 256) / 256) / 256) / 256) / 256)
    by (rewrite !Z.div_div by lia; reflexivity).
  replace (n / 2 ^ 64) with ((((((((n / 256) / 256) / 256) / 256) / 256) / 256) / 256) / 256)
    in H64 by (rewrite !Z.div_div by lia; reflexivity).
  set (q1 := n / 256) in *. set (q2 := q1 / 256) in *. set (q3 := q2 / 256) in *.
  set (q4 := q3 / 256) in *. set (q5 := q4 / 256) in *. set (q6 := q5 / 256) in *.
  set (q7 := q6 / 256) in *.
  pose proof (Hm n) as E0. pose proof (Hm q1) as E1. pose proof (Hm q2) as E2.
  pose proof (Hm q3) as E3. pose proof (Hm q4) as E4. pose proof (Hm q5) as E5.
  pose proof (Hm q6) as E6. pose proof (Hm q7) as E7.
  fold q1 in E0. fold q2 in E1. fold q3 in E2. fold q4 in E3. fold q5 in E4.
  fold q6 in E5. fold q7 in E6. rewrite H64 in E7.
  clearbody q1 q2 q3 q4 q5 q6 q7. lia.
Qed.

(* A 16-byte option record as the return block copies it: value word, tag
   byte (1 for a present value, 0 for the None constant), seven bytes of
   padding the contract leaves free. *)
Definition parentHeaderOptionRecord (record : list byte) (value : option Z) : Prop :=
  length record = 16%nat /\ optionalWordAt record 0 8 value.

(* The 80 result bytes the success return slots store: words at 0, 8, 16
   (x21, x22, x20: gas limit, gas used, timestamp), the base-fee, blob-gas
   and excess-blob-gas records at 24, 40, 56, the tag half-word 0 at 72, and
   six free bytes. *)
Definition parentHeaderSuccessBytes (gasLimit gasUsed timestamp : bv 64)
    (baseFee blobGas excessBlobGas : list byte) (tail : list byte) : list byte :=
  parentHeaderWordBytes gasLimit ++ parentHeaderWordBytes gasUsed ++
  parentHeaderWordBytes timestamp ++ baseFee ++ blobGas ++ excessBlobGas ++
  [BV 8 0; BV 8 0] ++ tail.

Lemma optionRecordAt (prefix record rest : list byte) (value : option Z) :
  parentHeaderOptionRecord record value ->
  optionalWordAt (prefix ++ record ++ rest) (length prefix) (length prefix + 8) value.
Proof.
  intros [Hlen [Htag Hval]]. split.
  - unfold byteAt in *. rewrite nth_error_app2 by lia.
    replace (length prefix + 8 - length prefix)%nat with 8%nat by lia.
    rewrite nth_error_app1 by lia. exact Htag.
  - destruct value as [n|]; [|exact I]. destruct Hval as [H8 Hv].
    unfold word64At. rewrite drop_app_length. rewrite take_app_le by lia.
    cbn [drop] in H8, Hv. split; assumption.
Qed.

Lemma wordAt (prefix rest : list byte) (w : bv 64) :
  word64At (prefix ++ parentHeaderWordBytes w ++ rest) (length prefix) (bv_unsigned w).
Proof.
  unfold word64At. rewrite drop_app_length.
  rewrite take_app_le by (rewrite parentHeaderWordBytesLength; lia).
  rewrite take_ge by (rewrite parentHeaderWordBytesLength; lia).
  split; [reflexivity|]. apply parentHeaderWordBytesValue.
Qed.

Lemma parentHeaderSuccessResult (bytes : list byte) (header : ParentHeaderValue)
    (gasLimit gasUsed timestamp : bv 64) (baseFee blobGas excessBlobGas tail : list byte) :
  candidateParentHeader bytes = candidateHeaderSuccess header ->
  bv_unsigned gasLimit = parentGasLimit header ->
  bv_unsigned gasUsed = parentGasUsed header ->
  bv_unsigned timestamp = parentTimestamp header ->
  parentHeaderOptionRecord baseFee (parentBaseFee header) ->
  parentHeaderOptionRecord blobGas (parentBlobGas header) ->
  parentHeaderOptionRecord excessBlobGas (parentExcessBlobGas header) ->
  length tail = 6%nat ->
  parentHeaderCandidateResult bytes
    (parentHeaderSuccessBytes gasLimit gasUsed timestamp baseFee blobGas excessBlobGas tail).
Proof.
  intros Hc Hgl Hgu Hts Hbf Hbg Heb Htail.
  apply (parentHeaderCandidateResultSuccess _ _ header Hc).
  pose proof Hbf as (Lbf & _). pose proof Hbg as (Lbg & _). pose proof Heb as (Leb & _).
  unfold parentHeaderSuccessBytes, parentHeaderResult80, parentHeaderResult72.
  set (W := parentHeaderWordBytes).
  assert (LW : forall w, length (W w) = 8%nat) by reflexivity.
  set (X := W gasLimit ++ W gasUsed ++ W timestamp ++ baseFee ++ blobGas ++ excessBlobGas).
  assert (LX : length X = 72%nat)
    by (unfold X; rewrite !length_app, !LW, Lbf, Lbg, Leb; reflexivity).
  replace (W gasLimit ++ W gasUsed ++ W timestamp ++ baseFee ++ blobGas ++ excessBlobGas ++
    [BV 8 0; BV 8 0] ++ tail) with (X ++ [BV 8 0; BV 8 0] ++ tail)
    by (unfold X; rewrite <- !app_assoc; reflexivity).
  assert (WA : forall pre w post off, off = length pre -> X = pre ++ W w ++ post ->
    word64At X off (bv_unsigned w)) by (intros ? ? ? ? -> ->; apply wordAt).
  assert (OA : forall pre r post v off, parentHeaderOptionRecord r v -> off = length pre ->
    X = pre ++ r ++ post -> optionalWordAt X off (off + 8) v)
    by (intros ? ? ? ? ? H -> ->; apply optionRecordAt, H).
  rewrite take_app_le by lia. rewrite take_ge by lia.
  assert (O1 : optionalWordAt X 24 32 (parentBaseFee header)).
  { apply (OA (W gasLimit ++ W gasUsed ++ W timestamp) baseFee (blobGas ++ excessBlobGas) _ 24%nat);
      [exact Hbf|reflexivity|unfold X; rewrite <- !app_assoc; reflexivity]. }
  assert (O2 : optionalWordAt X 40 48 (parentBlobGas header)).
  { apply (OA (W gasLimit ++ W gasUsed ++ W timestamp ++ baseFee) blobGas excessBlobGas _ 40%nat);
      [exact Hbg|rewrite !length_app, !LW, Lbf; reflexivity
      |unfold X; rewrite <- !app_assoc; reflexivity]. }
  assert (O3 : optionalWordAt X 56 64 (parentExcessBlobGas header)).
  { apply (OA (W gasLimit ++ W gasUsed ++ W timestamp ++ baseFee ++ blobGas) excessBlobGas [] _ 56%nat);
      [exact Heb|rewrite !length_app, !LW, Lbf, Lbg; reflexivity
      |unfold X; rewrite app_nil_r, <- !app_assoc; reflexivity]. }
  refine (conj _ (conj (conj LX (conj _ (conj _ (conj _ (conj O1 (conj O2 O3)))))) (conj _ _))).
  - rewrite length_app, LX, length_app, Htail. reflexivity.
  - rewrite <- Hgl. apply (WA [] _ (W gasUsed ++ W timestamp ++ baseFee ++ blobGas ++ excessBlobGas));
      reflexivity.
  - rewrite <- Hgu. apply (WA (W gasLimit) _ (W timestamp ++ baseFee ++ blobGas ++ excessBlobGas));
      reflexivity.
  - rewrite <- Hts. apply (WA (W gasLimit ++ W gasUsed) _ (baseFee ++ blobGas ++ excessBlobGas));
      [reflexivity|unfold X; rewrite <- !app_assoc; reflexivity].
  - unfold byteAt. rewrite nth_error_app2 by lia. rewrite LX. reflexivity.
  - unfold byteAt. rewrite nth_error_app2 by lia. rewrite LX. reflexivity.
Qed.
