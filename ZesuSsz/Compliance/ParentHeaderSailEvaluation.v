(* Plan step 2.4, M2: Sail evaluation of decodeParentHeader.
   sailParentHeaderModel_holds proves SailParentHeaderModel of
   ParentHeaderSailAgreement.v: the monadic Sail run sailParentHeaderRun
   (rlp_node_cursor, then _rec_decode_parent_header_fields of the pinned
   generated/evm-sail-coq/rlp/evm_rlp.v) computes the pure model
   sailPureParentHeader on every input shorter than 2^31 bytes. Method of
   DecodeItemSailEvaluation.v (runPrompt rewriting with sail_run_bind),
   lifted to an arbitrary input window sailWindow bytes base len:
   item header (rlp_ref_hdr, rlp_uint64_width), rlp_decode_item, the
   canonical-form check (rlp_item_uint_canonical, both framing branches),
   rlp_decode_word, rlp_decode_u256, rlp_decode_uint64, the profile read
   (blob schedule maximum 21, excess blob gas limit 2992193280, by
   vm_compute on the closed default profile), the walk over the items after
   field 18 (phSkipLoop) and the field loop (phFieldLoop, induction on the
   remaining field count, one case per field index).
   candidateParentHeader_sail_from_cover is the plan's M2 statement with the
   single premise KnownBugTriggersCoverDivergences.
   No host premise is used. Owner: contract fact (evaluation of the pinned
   Sail decoder). *)
From Coq Require Import Bool List String ZArith Lia.
From stdpp Require Import bitvector.definitions.
Require Import SailStdpp.MachineWord SailStdpp.Values SailStdpp.Prompt_monad SailStdpp.Prompt.
Require Import SailStdpp.Operators_mwords.
Require Import EvmSailRlp.evm_rlp_types EvmSailRlp.evm_rlp.
Require Import ZesuSsz.Compliance.SailRun.
Require Import ZesuSsz.Compliance.RlpInputBounds.
Require Import ZesuSsz.Automation.SailEval.
Require Import ZesuSsz.Contracts.RlpDecodeItem.
Import ListNotations.
Open Scope Z_scope.
Open Scope list_scope.

Definition sailWindow (bytes : list byte) (base len : Z) : list byte :=
  firstn (Z.to_nat len) (skipn (Z.to_nat base) bytes).

Definition sliceIn (bytes : list byte) (base len : Z) : Prop :=
  0 <= base /\ 0 <= len /\ base + len <= Z.of_nat (List.length bytes) /\
  Z.of_nat (List.length bytes) < 2 ^ 31.

Lemma sailWindowLength bytes base len :
  sliceIn bytes base len -> Z.of_nat (List.length (sailWindow bytes base len)) = len.
Proof.
  intros (Hb & Hl & Hfit & _). unfold sailWindow.
  rewrite firstn_length_le; [lia|]. rewrite skipn_length; lia.
Qed.

Lemma sailWindowSub bytes base len a c :
  sliceIn bytes base len -> 0 <= a -> 0 <= c -> a + c <= len ->
  sailWindow bytes (base + a) c =
    firstn (Z.to_nat c) (skipn (Z.to_nat a) (sailWindow bytes base len)).
Proof.
  intros (Hb & Hl & Hfit & _) Ha Hc Hac. unfold sailWindow.
  rewrite skipn_firstn_comm, firstn_firstn, skipn_skipn.
  replace (Z.to_nat (base + a)) with (Z.to_nat a + Z.to_nat base)%nat by lia.
  f_equal. lia.
Qed.

Lemma sliceInSub bytes base len a c :
  sliceIn bytes base len -> 0 <= a -> 0 <= c -> a + c <= len ->
  sliceIn bytes (base + a) c.
Proof. unfold sliceIn. lia. Qed.

Lemma nthFirstn {A} (l : list A) n k d : (k < n)%nat -> nth k (firstn n l) d = nth k l d.
Proof.
  revert l k. induction n as [|n IH]; intros [|x l] [|k] Hk; cbn; auto; try lia.
  apply IH. lia.
Qed.

Lemma nthSkipn {A} (l : list A) b k d : nth k (skipn b l) d = nth (b + k) l d.
Proof.
  revert l. induction b as [|b IH]; intros [|x l]; cbn; auto.
  destruct k; reflexivity.
Qed.

Lemma phSliceByte bytes base len (s : StatelessInputSliceFields base len) off rs :
  register_lookup shim_input_bytes rs = bytes -> sliceIn bytes base len ->
  0 <= off < len ->
  runPrompt (stateless_input_slice_byte s off) rs true =
    (Success (nth (Z.to_nat off) (sailWindow bytes base len) (BV 8 0)), rs).
Proof.
  intros Hrs Hin Hoff. pose proof Hin as (Hb & Hl & Hfit & _).
  unfold stateless_input_slice_byte.
  rewrite (proj2 (Z.ltb_lt off len) ltac:(lia)).
  unfold stateless_input_byte_at. cbn [stateless_input_length_value].
  cbn [and_boolM returnM SailStdpp.Prompt_monad.returnm SailStdpp.Prompt_monad.bind
    read_reg SailStdpp.Prompt_monad.read_reg runPrompt].
  rewrite (proj2 (Z.leb_le 0 base) Hb), (proj2 (Z.leb_le 0 len) Hl).
  cbn [SailStdpp.Prompt_monad.bind runPrompt].
  rewrite Hrs, shimInputLengthExact, (proj2 (Z.leb_le _ _) Hfit).
  cbn [assert_exp' SailStdpp.Prompt_monad.bind runPrompt].
  rewrite (proj2 (Z.leb_le 0 off) ltac:(lia)), (proj2 (Z.ltb_lt off len) ltac:(lia)).
  cbn [assert_exp' andb SailStdpp.Prompt_monad.bind runPrompt].
  try rewrite Hrs. apply sail_run_shim_byte; [lia|].
  unfold sailWindow. rewrite nthFirstn by lia. rewrite nthSkipn.
  replace (Z.to_nat (base + off)) with (Z.to_nat base + Z.to_nat off)%nat by lia.
  rewrite ?Hrs; apply nth_error_nth'. lia.
Qed.

Lemma firstnSnoc {A} (l : list A) n d :
  (n < List.length l)%nat -> firstn (S n) l = firstn n l ++ [nth n l d].
Proof.
  revert n. induction l as [|x l IH]; intros [|n] Hn; cbn in *; try lia; auto.
  rewrite <- IH by lia. reflexivity.
Qed.

Lemma bigEndianFirstnS (l : list byte) n :
  (n < List.length l)%nat ->
  bigEndian (firstn (S n) l) = 256 * bigEndian (firstn n l) + bv_unsigned (nth n l (BV 8 0)).
Proof.
  intros Hn. unfold bigEndian.
  rewrite (firstnSnoc l n (BV 8 0)) by exact Hn. rewrite fold_left_app. reflexivity.
Qed.

Lemma phRecWidth bytes base len (s : StatelessInputSliceFields base len) rs (n : nat) fuel acc :
  register_lookup shim_input_bytes rs = bytes -> sliceIn bytes base len ->
  Z.of_nat n <= len -> Z.of_nat n <= fuel ->
  runPrompt (_rec_rlp_uint64_width s (Z.of_nat n) fuel acc) rs true =
    (Success (bigEndian (firstn n (sailWindow bytes base len))), rs).
Proof.
  intros Hrs Hin. revert fuel acc. induction n as [|n IH]; intros fuel acc Hn Hfuel;
    destruct acc as [acc]; cbn [_rec_rlp_uint64_width].
  - rewrite sail_run_bind, (sail_run_assert_true _ _ (proj2 (Z.geb_ge fuel 0) ltac:(lia))).
    reflexivity.
  - rewrite sail_run_bind, (sail_run_assert_true _ _ (proj2 (Z.geb_ge fuel 0) ltac:(lia))).
    cbv beta. rewrite (proj2 (Z.eqb_neq (Z.of_nat (S n)) 0) ltac:(lia)).
    rewrite sail_run_bind.
    replace (Z.of_nat (S n) - 1) with (Z.of_nat n) by lia.
    rewrite IH by lia. cbv beta iota.
    rewrite sail_run_bind, (phSliceByte bytes) by (auto; lia). cbv beta iota.
    cbn [returnM SailStdpp.Prompt_monad.returnm runPrompt].
    unfold rlp_uint64_append. rewrite sail_uint_unsigned.
    replace (Z.to_nat (Z.of_nat n)) with n by lia.
    rewrite bigEndianFirstnS by (pose proof (sailWindowLength _ _ _ Hin); lia).
    f_equal. f_equal. lia.
Qed.

Require Import ZesuSsz.Compliance.KnownBugs ZesuSsz.Contracts.ParentHeader.
Require Import ZesuSsz.Contracts.Candidates.ParentHeaderDomain.
Require Import ZesuSsz.Contracts.Candidates.ParentHeaderCandidate.
Require Import ZesuSsz.Contracts.ParentHeaderBugTriggers.
Require Import ZesuSsz.Compliance.ProjectionParentHeader.
Require Import ZesuSsz.Contracts.ParentHeaderRung2.
Require Import ZesuSsz.Compliance.ParentHeaderSailAgreement.

Lemma phRecWidthZ bytes base len (s : StatelessInputSliceFields base len) rs w fuel acc :
  register_lookup shim_input_bytes rs = bytes -> sliceIn bytes base len ->
  0 <= w -> w <= len -> w <= fuel ->
  runPrompt (_rec_rlp_uint64_width s w fuel acc) rs true =
    (Success (bigEndian (firstn (Z.to_nat w) (sailWindow bytes base len))), rs).
Proof.
  intros Hrs Hin Hw Hwl Hwf.
  pose proof (phRecWidth bytes base len s rs (Z.to_nat w) fuel acc Hrs Hin) as H.
  rewrite Z2Nat.id in H by lia. apply H; lia.
Qed.

Definition sailRefHdr (r : list byte) : option (bool * Z * Z) :=
  match r with
  | [] => None
  | prefix :: rest =>
      let h := bv_unsigned prefix in
      if h <? 128 then Some (false, 0, 1)
      else if h <? 184 then Some (false, 1, h - 128)
      else if h <? 192 then
        if h - 183 <=? Z.of_nat (List.length r) - 1
        then Some (false, 1 + (h - 183), bigEndian (firstn (Z.to_nat (h - 183)) rest))
        else None
      else if h <? 248 then Some (true, 1, h - 192)
      else if h - 247 <=? Z.of_nat (List.length r) - 1
        then Some (true, 1 + (h - 247), bigEndian (firstn (Z.to_nat (h - 247)) rest))
        else None
  end.

Definition hdrOutcome (o : option (bool * Z * Z)) : SailOutcome (bool * source_pointer * Z) :=
  match o with
  | Some (l, h, p) => Success (l, Build_source_pointer h, p)
  | None => Reject RlpDecode
  end.

Lemma phLengthBytes bytes base len (s : StatelessInputSliceFields base len) rs prefix rest w :
  register_lookup shim_input_bytes rs = bytes -> sliceIn bytes base len ->
  sailWindow bytes base len = prefix :: rest -> 0 <= w <= len - 1 ->
  runPrompt (rlp_uint64_width (stateless_input_sub_slice s 1 w) w) rs true =
    (Success (bigEndian (firstn (Z.to_nat w) rest)), rs).
Proof.
  intros Hrs Hin Hw Hwl. unfold rlp_uint64_width.
  assert (Hsub : sliceIn bytes (base + 1) w) by (apply sliceInSub with (len := len); auto; lia).
  rewrite (phRecWidthZ bytes (base + 1) w _ rs w w _ Hrs Hsub) by lia.
  rewrite (sailWindowSub bytes base len 1 w) by (auto; lia). rewrite Hw.
  cbn [skipn Z.to_nat Pos.to_nat Pos.iter_op Nat.add]. rewrite firstn_firstn, Nat.min_id.
  reflexivity.
Qed.

Lemma phRefHdr bytes base len (s : StatelessInputSliceFields base len) rs :
  register_lookup shim_input_bytes rs = bytes -> sliceIn bytes base len ->
  StatelessInputSliceFields_len s = len ->
  runPrompt (rlp_ref_hdr s) rs true =
    (hdrOutcome (sailRefHdr (sailWindow bytes base len)), rs).
Proof.
  intros Hrs Hin Hs. pose proof (sailWindowLength _ _ _ Hin) as Hwl.
  unfold rlp_ref_hdr. rewrite Hs.
  destruct (sailWindow bytes base len) as [|prefix rest] eqn:Hw.
  - cbn in Hwl. subst len. reflexivity.
  - cbn [List.length] in Hwl. rewrite (proj2 (Z.eqb_neq len 0)) by lia.
    cbn [SailStdpp.Prompt_monad.bind0 SailStdpp.Prompt_monad.bind returnM
      SailStdpp.Prompt_monad.returnm runPrompt].
    rewrite sail_run_bind_assoc, sail_run_bind, (phSliceByte bytes base len) by (auto; lia).
    rewrite Hw. change (Z.to_nat 0) with 0%nat. cbn [nth]. cbv beta. rewrite sail_uint_unsigned.
    cbn [sailRefHdr]. cbn [List.length]. rewrite Hwl.
    pose proof (bv_unsigned_in_range _ prefix) as Hrange.
    destruct (bv_unsigned prefix <? 128) eqn:E1; [reflexivity|].
    destruct (bv_unsigned prefix <? 184) eqn:E2; [reflexivity|].
    destruct (bv_unsigned prefix <? 192) eqn:E3.
    + destruct (bv_unsigned prefix - 183 <=? len - 1) eqn:E4; [|reflexivity].
      apply Z.leb_le in E4. apply Z.ltb_ge in E2.
      rewrite sail_run_bind_assoc, sail_run_bind, (phLengthBytes bytes base len s rs prefix rest) by (auto; lia).
      reflexivity.
    + destruct (bv_unsigned prefix <? 248) eqn:E5; [reflexivity|].
      destruct (bv_unsigned prefix - 247 <=? len - 1) eqn:E4; [|reflexivity].
      apply Z.leb_le in E4. apply Z.ltb_ge in E5.
      rewrite sail_run_bind_assoc, sail_run_bind, (phLengthBytes bytes base len s rs prefix rest) by (auto; lia).
      reflexivity.
Qed.

Ltac phBoolFacts :=
  repeat match goal with
  | H : (_ <? _) = true |- _ => apply Z.ltb_lt in H
  | H : (_ <? _) = false |- _ => apply Z.ltb_ge in H
  | H : (_ <=? _) = true |- _ => apply Z.leb_le in H
  | H : (_ <=? _) = false |- _ => apply Z.leb_gt in H
  | H : (_ =? _) = true |- _ => apply Z.eqb_eq in H
  | H : (_ =? _) = false |- _ => apply Z.eqb_neq in H
  end.

Lemma sailDecodeItemHdr r :
  Z.of_nat (List.length r) < 2 ^ 31 ->
  sailDecodeItem r =
    match sailRefHdr r with
    | Some (l, h, p) =>
        if h + p <=? Z.of_nat (List.length r) then candidateSuccess l h p else candidateError
    | None => candidateError
    end.
Proof.
  intros Hlen. destruct r as [|prefix rest]; [reflexivity|].
  unfold sailDecodeItem, candidateDecodeItem, sailRefHdr, checkedPayload.
  unfold word64Modulus.
  pose proof (bv_unsigned_in_range _ prefix) as Hrange.
  pose proof (bigEndianNonneg (firstn (Z.to_nat (bv_unsigned prefix - 183)) rest)).
  pose proof (bigEndianNonneg (firstn (Z.to_nat (bv_unsigned prefix - 247)) rest)).
  repeat (cbv zeta; match goal with |- context [if ?c then _ else _] => destruct c eqn:? end; phBoolFacts);
    first [reflexivity | exfalso; lia | f_equal; lia | idtac].
Qed.

Lemma sailRefHdrNonneg r l h p :
  sailRefHdr r = Some (l, h, p) -> 0 <= h <= 9 /\ 0 <= p /\ 0 < h + p /\
    (h = 0 /\ p = 1 \/ 1 <= h).
Proof.
  destruct r as [|prefix rest]; [discriminate|]. unfold sailRefHdr.
  pose proof (bv_unsigned_in_range _ prefix) as Hrange.
  pose proof (bigEndianNonneg (firstn (Z.to_nat (bv_unsigned prefix - 183)) rest)).
  pose proof (bigEndianNonneg (firstn (Z.to_nat (bv_unsigned prefix - 247)) rest)).
  repeat (cbv zeta; match goal with |- context [if ?c then _ else _] => destruct c eqn:? end; phBoolFacts);
    intros Heq; inversion Heq; subst; change (MachineWord.Z_idx 8) with 8%N in *; unfold bv_modulus in *; cbn [Z.of_N] in *; lia.
Qed.

Lemma phSourceLenAutocast base base' len (x : StatelessInputSliceFields base' len) :
  base' = base ->
  StatelessInputSliceFields_len
    (@TypeCasts.autocast (fun b => StatelessInputSliceFields b len) base' base _ x) =
  StatelessInputSliceFields_len x.
Proof.
  intros Heq. unfold TypeCasts.autocast.
  destruct (Z.eq_dec base' base) as [e|e]; [|contradiction].
  destruct e. rewrite TypeCasts.cast_Z_refl. reflexivity.
Qed.

Definition phFieldOk {base full content} (field : RlpFieldRef base full content)
    (isList : bool) (p : Z) : Prop :=
  RlpFieldRef_is_list field = isList /\ RlpFieldRef_content_len field = p /\
  StatelessInputSliceFields_len (RlpFieldRef_source field) = full.

Lemma phDecodeItem bytes base len (s : StatelessInputSliceFields base len) rs :
  register_lookup shim_input_bytes rs = bytes -> sliceIn bytes base len ->
  StatelessInputSliceFields_len s = len ->
  match sailDecodeItem (sailWindow bytes base len) with
  | candidateError => runPrompt (rlp_decode_item s) rs true = (Reject RlpDecode, rs)
  | candidateSuccess isList h p =>
      exists field : RlpFieldRef base (h + p) p,
        runPrompt (rlp_decode_item s) rs true =
          (Success (@existT Z (fun full => {content : Z & RlpFieldRef base full content})
            (h + p) (@existT Z (fun content => RlpFieldRef base (h + p) content) p field)), rs) /\
        phFieldOk field isList p
  end.
Proof.
  intros Hrs Hin Hs. pose proof (sailWindowLength _ _ _ Hin) as Hwl.
  pose proof Hin as (Hb0 & Hl0 & Hfit0 & Hbig).
  pose proof (phRefHdr bytes base len s rs Hrs Hin Hs) as Hhdr.
  rewrite sailDecodeItemHdr by lia.
  unfold rlp_decode_item.
  destruct (sailWindow bytes base len) as [|prefix rest] eqn:Hw.
  - cbn in Hwl. subst len. reflexivity.
  - rewrite (proj2 (Z.eqb_neq len 0)) by (cbn [List.length] in Hwl; lia).
    cbn [SailStdpp.Prompt_monad.bind0 SailStdpp.Prompt_monad.bind returnM
      SailStdpp.Prompt_monad.returnm runPrompt].
    rewrite sail_run_bind_assoc, sail_run_bind, Hhdr. rewrite Hwl.
    destruct (sailRefHdr (prefix :: rest)) as [[[l h] p]|] eqn:Hh; [|reflexivity].
    pose proof (sailRefHdrNonneg _ _ _ _ Hh) as ((Hh0 & _) & Hp0 & Hhp & _).
    cbn [hdrOutcome]. cbv beta iota.
    cbn [SailStdpp.Prompt_monad.bind0 SailStdpp.Prompt_monad.bind returnM
      SailStdpp.Prompt_monad.returnm runPrompt source_pointer_value].
    destruct (h + p <=? len) eqn:Hfit; phBoolFacts.
    + rewrite (proj2 (Z.ltb_ge len h)) by lia.
      rewrite (proj2 (Z.ltb_ge (len - h) p)) by lia.
      cbn [SailStdpp.Prompt_monad.bind0 SailStdpp.Prompt_monad.bind returnM
        SailStdpp.Prompt_monad.returnm runPrompt].
      cbv beta zeta. try rewrite (proj2 (Z.ltb_lt 0 (h + p))) by lia.
      try rewrite (proj2 (Z.leb_le (h + p) len)) by lia.
      cbn [andb]. eexists. split; [reflexivity|].
      repeat split; cbn [RlpFieldRef_is_list RlpFieldRef_content_len RlpFieldRef_source].
      rewrite phSourceLenAutocast by lia. reflexivity.
    + destruct (len <? h) eqn:Hlt; [reflexivity|]. phBoolFacts.
      rewrite (proj2 (Z.ltb_lt (len - h) p)) by lia. reflexivity.
Qed.

Lemma sliceInPrefix bytes base len c :
  sliceIn bytes base len -> 0 <= c <= len -> sliceIn bytes base c.
Proof. unfold sliceIn. lia. Qed.

Lemma sailWindowPrefix bytes base len c :
  sliceIn bytes base len -> 0 <= c <= len ->
  sailWindow bytes base c = firstn (Z.to_nat c) (sailWindow bytes base len).
Proof.
  intros Hin Hc. unfold sailWindow. rewrite firstn_firstn. f_equal. lia.
Qed.

Lemma phSliceBytePrefix bytes base len c (s : StatelessInputSliceFields base c) off rs :
  register_lookup shim_input_bytes rs = bytes -> sliceIn bytes base len ->
  c <= len -> 0 <= off < c ->
  runPrompt (stateless_input_slice_byte s off) rs true =
    (Success (nth (Z.to_nat off) (sailWindow bytes base len) (BV 8 0)), rs).
Proof.
  intros Hrs Hin Hc Hoff.
  rewrite (phSliceByte bytes base c s off rs Hrs) by (try apply (sliceInPrefix _ _ len); auto; lia).
  rewrite (sailWindowPrefix bytes base len c) by (auto; lia).
  rewrite nthFirstn by lia. reflexivity.
Qed.

Lemma phEqVec8 {n} (x y : mword n) : eq_vec x y = (bv_unsigned x =? bv_unsigned y).
Proof.
  unfold eq_vec, MachineWord.eqb, get_word.
  destruct (Z.eqb_spec (bv_unsigned x) (bv_unsigned y)) as [E|E].
  - apply bool_decide_true. apply bv_eq. exact E.
  - apply bool_decide_false. intros Hxy. apply E. rewrite Hxy. reflexivity.
Qed.

Lemma phOx80 : bv_unsigned (Ox"80" : mword 8) = 128.
Proof. reflexivity. Qed.
Lemma phOx00 : bv_unsigned (Ox"00" : mword 8) = 0.
Proof. reflexivity. Qed.

Lemma phAddLength (x : mword 8) (p : Z) : bv_unsigned x = 128 -> 0 <= p <= 55 ->
  bv_unsigned (add_vec x (rlp_nat_length_byte p)) = 128 + p.
Proof.
  intros Hx Hp. unfold add_vec, word_binop, with_word', with_word, MachineWord.add.
  rewrite bv_add_unsigned. unfold rlp_nat_length_byte.
  rewrite sail_get_slice_int by lia. rewrite Z_to_bv_unsigned.
  change (bv_unsigned (x : MachineWord.word (MachineWord.Z_idx 8))) with (bv_unsigned x).
  rewrite Hx.
  rewrite Z.shiftr_0_r. unfold bv_wrap, bv_modulus. cbn [Z.to_N MachineWord.Z_idx Z.of_N].
  rewrite (Z.mod_small p) by lia. rewrite Z.mod_small by lia. reflexivity.
Qed.

Lemma phOx80' : bv_unsigned (MachineWord.N_to_word 8 (HexString.Raw.to_N "80" 0)) = 128.
Proof. reflexivity. Qed.
Lemma phOx00' : bv_unsigned (MachineWord.N_to_word 8 (HexString.Raw.to_N "00" 0)) = 0.
Proof. reflexivity. Qed.

Lemma phBit7 (x : mword 8) :
  eq_vec (access_vec_dec x 7) ('b"0") = (bv_unsigned x <? 128).
Proof.
  rewrite phEqVec8.
  unfold access_vec_dec, access_mword_dec, MachineWord.slice, get_word.
  rewrite bv_extract_unsigned. change (bv_unsigned ('b"0" : mword 1)) with 0.
  pose proof (bv_unsigned_in_range _ x) as Hx. unfold bv_modulus in Hx.
  change (MachineWord.Z_idx 8) with 8%N in *. cbn [Z.of_N] in Hx.
  unfold bv_wrap, bv_modulus. rewrite Z.shiftr_div_pow2 by lia.
  cbn [MachineWord.Z_idx Z.to_N Z.of_N].
  destruct (Z.ltb_spec (bv_unsigned x) 128); change (MachineWord.Z_idx 8) with 8%N in *.
  - rewrite Z.div_small by lia. rewrite (proj2 (Z.ltb_lt _ _) H). reflexivity.
  - replace (bv_unsigned x / 2 ^ 7) with 1.
    + rewrite (proj2 (Z.ltb_ge _ _) H). reflexivity.
    + change (2 ^ 7) with 128. change (2 ^ 8) with 256 in Hx. apply Z.div_unique with (r := bv_unsigned x - 128); [left|]; change (MachineWord.Z_idx 8) with 8%N in *; lia.
Qed.

Ltac phN := change (MachineWord.Z_idx 8) with 8%N in *.

Ltac phBoolFacts2 :=
  repeat match goal with
  | H : (_ && _) = true |- _ => apply andb_true_iff in H as [? ?]
  | H : (_ && _) = false |- _ => apply andb_false_iff in H as [?|?]
  | H : negb _ = true |- _ => apply negb_true_iff in H
  | H : negb _ = false |- _ => apply negb_false_iff in H
  | H : (_ <? _) = true |- _ => apply Z.ltb_lt in H
  | H : (_ <? _) = false |- _ => apply Z.ltb_ge in H
  | H : (_ <=? _) = true |- _ => apply Z.leb_le in H
  | H : (_ <=? _) = false |- _ => apply Z.leb_gt in H
  | H : (_ =? _) = true |- _ => apply Z.eqb_eq in H
  | H : (_ =? _) = false |- _ => apply Z.eqb_neq in H
  end.

Lemma phCanonModel r h p :
  0 <= h -> 0 <= p <= 55 -> 0 < h + p -> h + p <= Z.of_nat (List.length r) ->
  sailShortUintCanonical r false h p =
    if p =? 0 then (h =? 1) && (bv_unsigned (nth 0 r (BV 8 0)) =? 128)
    else negb (bv_unsigned (nth (Z.to_nat h) r (BV 8 0)) =? 0) &&
      (if (p =? 1) && (bv_unsigned (nth (Z.to_nat h) r (BV 8 0)) <? 128) then h =? 0
       else (h =? 1) && (bv_unsigned (nth 0 r (BV 8 0)) =? 128 + p)).
Proof.
  intros Hh Hp Hhp Hfit.
  destruct r as [|first rest]; [cbn in Hfit; lia|].
  unfold sailShortUintCanonical, itemPayload.
  rewrite (proj2 (Z.leb_le p 55)) by lia. cbn [negb andb].
  destruct (firstn (Z.to_nat p) (skipn (Z.to_nat h) (first :: rest))) as [|lead tl] eqn:Hpl.
  - assert (Hp0 : p = 0).
    { apply (f_equal (@List.length byte)) in Hpl. rewrite firstn_length_le in Hpl.
      - cbn in Hpl. lia.
      - rewrite skipn_length; cbn [List.length] in *; lia. }
    subst p. reflexivity.
  - assert (Hpn : p <> 0).
    { intros ->. cbn in Hpl. discriminate. }
    assert (Hlead : lead = nth (Z.to_nat h) (first :: rest) (BV 8 0)).
    { apply (f_equal (fun l => nth 0 l (BV 8 0))) in Hpl. cbn [nth] in Hpl.
      rewrite <- Hpl. rewrite nthFirstn by lia.
      rewrite nthSkipn. f_equal. lia. }
    rewrite (proj2 (Z.eqb_neq p 0) Hpn). rewrite <- Hlead. cbn [negb andb nth]. reflexivity.
Qed.

Ltac phEvalStep Hrs Hin :=
  first
  [ rewrite sail_run_bind_assoc
  | rewrite sail_run_bind
  | progress cbn [SailStdpp.Prompt_monad.bind0 SailStdpp.Prompt_monad.bind returnM
      SailStdpp.Prompt_monad.returnm runPrompt SailStdpp.Prompt.and_boolM
      SailStdpp.Prompt.or_boolM fatal_error SailStdpp.Prompt_monad.exit
      SailStdpp.Prompt_monad.assert_exp' read_reg SailStdpp.Prompt_monad.read_reg
      stateless_input_length_value word_byte_count_value]
  | rewrite (phSliceBytePrefix _ _ _ _ _ _ _ Hrs Hin) by (phN; lia)
  | progress unfold RLP_SHORT_LENGTH_LIMIT, RLP_WORD_LENGTH_LIMIT, RLP_UINT64_LENGTH_LIMIT,
      WORD_BYTE_LENGTH, EIGHT_BYTE_LENGTH
  | rewrite Hrs
  | rewrite shimInputLengthExact
  | match goal with |- context [runPrompt (if ?c then _ else _) _ _] => destruct c eqn:? end
  | match goal with |- context [runPrompt (SailStdpp.Prompt_monad.assert_exp' ?c _) _ _] =>
      destruct c eqn:? end ].

Ltac phCanonFinish h :=
  unfold neq_vec in *; rewrite ?Z.add_simpl_r in *; change (Z.to_nat 0) with 0%nat in *;
  rewrite ?phBit7 in *; rewrite ?phEqVec8 in *;
  rewrite ?phOx80, ?phOx00, ?phOx80', ?phOx00' in *;
  rewrite ?phAddLength in * by (first [reflexivity | lia]);
  phBoolFacts2; phN;
  try (assert (h = 0) by lia; subst h; change (Z.to_nat 0) with 0%nat in * );
  phN;
  repeat match goal with
    | |- context [?a =? ?b] => destruct (Z.eqb_spec a b)
    | |- context [?a <? ?b] => destruct (Z.ltb_spec a b)
    end;
  cbn [andb negb]; phN; first [reflexivity | exfalso; lia | idtac].

Local Opaque EvmSailRlp.evm_rlp._rec_shim_load_n EvmSailRlp.evm_rlp._rec_rlp_uint64_width.

Lemma phUintCanonical bytes base len rs h p (f : RlpFieldRef base (h + p) p) l :
  register_lookup shim_input_bytes rs = bytes -> sliceIn bytes base len ->
  RlpFieldRef_is_list f = l -> 0 <= h <= 9 -> 0 <= p -> 0 < h + p -> h + p <= len ->
  (h = 0 /\ p = 1 \/ 1 <= h) ->
  exists b, runPrompt (rlp_item_uint_canonical f) rs true = (Success b, rs) /\
    (p <= 55 -> b = sailShortUintCanonical (sailWindow bytes base len) l h p).
Proof.
  intros Hrs Hin Hl Hh Hp Hhp Hfit Hh0.
  pose proof (sailWindowLength _ _ _ Hin) as Hwl.
  pose proof Hin as (Hb0 & Hl0 & Hfit0 & Hbig).
  unfold rlp_item_uint_canonical, rlp_ref_bytes_canonical. rewrite Hl.
  destruct l.
  - cbn [SailStdpp.Prompt_monad.bind0 SailStdpp.Prompt_monad.bind returnM
      SailStdpp.Prompt_monad.returnm runPrompt SailStdpp.Prompt.and_boolM negb].
    eexists; split; [reflexivity|]. intros _. reflexivity.
  - unfold rlp_ref_framing_canonical. rewrite Hl.
    destruct (Z.leb_spec p 55) as [Hsmall|Hlarge].
    + rewrite phCanonModel by lia.
      repeat phEvalStep Hrs Hin;
        phBoolFacts2; phN; try (exfalso; lia);
        (eexists; split; [reflexivity|intros _]); phCanonFinish h.
    + unfold rlp_length_word, word_of_nat_byte_count.
      rewrite (proj2 (Z.ltb_lt p (pow2 256))) by
        (unfold pow2, pow; apply Z.lt_le_trans with (2 ^ 31); [lia|apply Z.pow_le_mono_r; lia]).
      unfold stateless_input_slice_load_n, stateless_input_load_n_word, shim_load_n.
      repeat ((rewrite (sail_run_shim_load_Z _ _ _ bytes) by (first [exact Hrs | phBoolFacts2; phN; lia]))
        || phEvalStep Hrs Hin);
        phBoolFacts2; phN; try (exfalso; lia);
        (eexists; split; [reflexivity|intros; lia]).
Qed.

Lemma phFoldUint (l : list byte) a :
  fold_left (fun acc (item : byte) => Z.add (Z.mul acc 256) (@uint 8 item)) l a =
  fold_left (fun acc (b : byte) => 256 * acc + bv_unsigned b) l a.
Proof.
  revert a. induction l as [|x l IH]; intros a; cbn [fold_left]; [reflexivity|].
  rewrite IH. f_equal. rewrite sail_uint_unsigned. phN. lia.
Qed.

Lemma phPayloadWindow bytes base len h p :
  sliceIn bytes base len -> 0 <= h -> 0 <= p -> h + p <= len ->
  firstn (Z.to_nat p) (skipn (Z.to_nat (base + (h + p - p))) bytes) =
  itemPayload (sailWindow bytes base len) h p.
Proof.
  intros Hin Hh Hp Hfit. rewrite Z.add_simpl_r.
  change (firstn (Z.to_nat p) (skipn (Z.to_nat (base + h)) bytes)) with (sailWindow bytes (base + h) p).
  rewrite (sailWindowSub bytes base len h p) by (auto; lia). reflexivity.
Qed.

Lemma phItemPayloadLength r h p :
  0 <= h -> 0 <= p -> h + p <= Z.of_nat (List.length r) ->
  List.length (itemPayload r h p) = Z.to_nat p.
Proof.
  intros Hh Hp Hfit. unfold itemPayload.
  rewrite firstn_length_le; [lia|]. rewrite skipn_length; lia.
Qed.

Lemma phBigEndian256 (l : list byte) :
  (List.length l <= 32)%nat -> 0 <= bigEndian l < 2 ^ 256.
Proof.
  intros Hl. split; [apply bigEndianNonneg|].
  eapply Z.lt_le_trans; [exact (proj2 (bigEndianFoldBound l 0 ltac:(lia)))|].
  change (2 ^ 256) with (256 ^ 32). rewrite Z.mul_1_l.
  apply Z.pow_le_mono_r; lia.
Qed.

Lemma phWordValue v : 0 <= v < 2 ^ 256 ->
  word_value (word_from_bits (get_slice_int 256 v 0)) = v.
Proof.
  intros Hv. unfold word_from_bits, u256. cbn [word_value].
  rewrite sail_uint_unsigned, sail_get_slice_int by lia.
  rewrite Z_to_bv_unsigned, Z.shiftr_0_r. unfold bv_wrap, bv_modulus.
  cbn [Z.to_N Z.of_N]. apply Z.mod_small. exact Hv.
Qed.

Lemma phDecodeWord bytes base len rs h p (f : RlpFieldRef base (h + p) p) l :
  register_lookup shim_input_bytes rs = bytes -> sliceIn bytes base len ->
  RlpFieldRef_is_list f = l -> 0 <= h <= 9 -> 0 <= p -> 0 < h + p -> h + p <= len ->
  runPrompt (rlp_decode_word f) rs true =
    (if l || (32 <? p) then Reject RlpDecode
     else Success (Build_word (bigEndian (itemPayload (sailWindow bytes base len) h p))), rs).
Proof.
  intros Hrs Hin Hl Hh Hp Hhp Hfit.
  pose proof (sailWindowLength _ _ _ Hin) as Hwl.
  pose proof Hin as (Hb0 & Hl0 & Hfit0 & Hbig).
  unfold rlp_decode_word, stateless_input_slice_load_n, stateless_input_load_n_word, shim_load_n.
  unfold RLP_WORD_LENGTH_LIMIT, WORD_BYTE_LENGTH. rewrite Hl.
  destruct (l || (32 <? p)) eqn:E; [reflexivity|].
  apply orb_false_iff in E as [El Ep]. apply Z.ltb_ge in Ep.
  repeat ((rewrite (sail_run_shim_load_Z _ _ _ bytes) by (first [exact Hrs | phBoolFacts2; phN; lia]))
    || phEvalStep Hrs Hin);
    phBoolFacts2; phN; try (exfalso; lia).
  - rewrite phFoldUint. change (fold_left (fun acc (b : byte) => 256 * acc + bv_unsigned b) ?l 0)
      with (bigEndian l).
    rewrite (phPayloadWindow bytes base len h p) by (auto; lia).
    rewrite phWordValue; [reflexivity|].
    apply phBigEndian256. rewrite phItemPayloadLength by lia. lia.
  - assert (p = 0) by lia. subst p. unfold itemPayload. rewrite firstn_O. reflexivity.
Qed.

Lemma phDecodeUint64 bytes base len rs h p (f : RlpFieldRef base (h + p) p) l :
  register_lookup shim_input_bytes rs = bytes -> sliceIn bytes base len ->
  RlpFieldRef_is_list f = l -> 0 <= h <= 9 -> 0 <= p -> 0 < h + p -> h + p <= len ->
  (h = 0 /\ p = 1 \/ 1 <= h) ->
  runPrompt (rlp_decode_uint64 f) rs true =
    (if sailShortUintCanonical (sailWindow bytes base len) l h p && (p <=? 8)
     then Success (Build_ssz_uint (bigEndian (itemPayload (sailWindow bytes base len) h p)))
     else Reject RlpDecode, rs).
Proof.
  intros Hrs Hin Hl Hh Hp Hhp Hfit Hh0.
  pose proof Hin as (Hb0 & Hl0 & Hfit0 & Hbig).
  destruct (phUintCanonical bytes base len rs h p f l Hrs Hin Hl Hh Hp Hhp Hfit Hh0) as [b [Hrun Hb]].
  unfold rlp_decode_uint64, RLP_UINT64_LENGTH_LIMIT, EIGHT_BYTE_LENGTH.
  rewrite sail_run_bind_assoc, sail_run_bind, Hrun. cbv beta iota.
  destruct (Z.leb_spec p 8) as [Hp8|Hp8].
  - rewrite (Hb ltac:(lia)).
    destruct (sailShortUintCanonical (sailWindow bytes base len) l h p); [|reflexivity].
    rewrite (proj2 (Z.ltb_ge 8 p) Hp8). cbn [negb orb andb].
    cbn [SailStdpp.Prompt_monad.bind0 SailStdpp.Prompt_monad.bind returnM
      SailStdpp.Prompt_monad.returnm runPrompt rlp_item_content].
    unfold rlp_uint64_width. rewrite Z.rem_small by lia.
    assert (Hsub : sliceIn bytes (base + (h + p - p)) p) by (unfold sliceIn in *; lia).
    rewrite sail_run_bind, (phRecWidthZ bytes (base + (h + p - p)) p _ rs p p _ Hrs Hsub) by lia.
    cbn [SailStdpp.Prompt_monad.bind returnM SailStdpp.Prompt_monad.returnm runPrompt].
    unfold sailWindow at 1. rewrite firstn_firstn, Nat.min_id.
    rewrite (phPayloadWindow bytes base len h p) by (auto; lia). reflexivity.
  - rewrite (proj2 (Z.ltb_lt 8 p)) by lia. rewrite orb_true_r.
    try rewrite (proj2 (Z.leb_gt p 8)) by lia. rewrite ?andb_false_r. reflexivity.
Qed.

Lemma phDecodeU256 bytes base len rs h p (f : RlpFieldRef base (h + p) p) l :
  register_lookup shim_input_bytes rs = bytes -> sliceIn bytes base len ->
  RlpFieldRef_is_list f = l -> 0 <= h <= 9 -> 0 <= p -> 0 < h + p -> h + p <= len ->
  (h = 0 /\ p = 1 \/ 1 <= h) ->
  runPrompt (rlp_decode_u256 f) rs true =
    (if sailShortUintCanonical (sailWindow bytes base len) l h p && (p <=? 32)
     then Success (Build_word (bigEndian (itemPayload (sailWindow bytes base len) h p)))
     else Reject RlpDecode, rs).
Proof.
  intros Hrs Hin Hl Hh Hp Hhp Hfit Hh0.
  destruct (phUintCanonical bytes base len rs h p f l Hrs Hin Hl Hh Hp Hhp Hfit Hh0) as [b [Hrun Hb]].
  unfold rlp_decode_u256.
  rewrite sail_run_bind_assoc, sail_run_bind, Hrun. cbv beta iota.
  destruct (Z.leb_spec p 32) as [Hp32|Hp32].
  - rewrite (Hb ltac:(lia)). try rewrite (proj2 (Z.leb_le p 32) Hp32). rewrite andb_true_r.
    destruct (sailShortUintCanonical (sailWindow bytes base len) l h p) eqn:Ec; [|reflexivity].
    assert (El : l = false) by (destruct l; [discriminate Ec|reflexivity]). subst l.
    cbv beta iota. rewrite sail_run_bind, (sail_run_bind (rlp_decode_word f)).
    rewrite (phDecodeWord bytes base len rs h p f false) by auto.
    rewrite (proj2 (Z.ltb_ge 32 p) Hp32). reflexivity.
  - try rewrite (proj2 (Z.leb_gt p 32)) by lia. rewrite andb_false_r.
    destruct b; [|reflexivity].
    cbv beta iota. rewrite sail_run_bind, (sail_run_bind (rlp_decode_word f)).
    rewrite (phDecodeWord bytes base len rs h p f l) by auto.
    rewrite (proj2 (Z.ltb_lt 32 p)) by lia. rewrite orb_true_r. reflexivity.
Qed.

Lemma phItemFacts r l h p :
  Z.of_nat (List.length r) < 2 ^ 31 ->
  sailDecodeItem r = candidateSuccess l h p ->
  0 <= h <= 9 /\ 0 <= p /\ 0 < h + p /\ h + p <= Z.of_nat (List.length r) /\
  (h = 0 /\ p = 1 \/ 1 <= h).
Proof.
  intros Hlen Hd. rewrite sailDecodeItemHdr in Hd by exact Hlen.
  destruct (sailRefHdr r) as [[[l' h'] p']|] eqn:Hh; [|discriminate].
  destruct (h' + p' <=? Z.of_nat (List.length r)) eqn:Hf; [|discriminate].
  inversion Hd; subst. apply Z.leb_le in Hf.
  pose proof (sailRefHdrNonneg _ _ _ _ Hh). tauto.
Qed.

Lemma sailWindowSuffix bytes base len a :
  sliceIn bytes base len -> 0 <= a <= len ->
  sailWindow bytes (base + a) (len - a) = skipn (Z.to_nat a) (sailWindow bytes base len).
Proof.
  intros Hin Ha. rewrite (sailWindowSub bytes base len a (len - a)) by (auto; lia).
  apply firstn_all2. pose proof (sailWindowLength _ _ _ Hin).
  rewrite skipn_length; lia.
Qed.

Lemma phEDiv v : e_div v (pow2 17) = v / 2 ^ 17.
Proof. unfold e_div, pow2, pow. change (Z.sgn (2 ^ 17)) with 1. change (Z.abs (2 ^ 17)) with (2 ^ 17). lia. Qed.

Ltac phProfileConstants :=
  repeat match goal with
  | |- context [BlobScheduleFields_max ?t] =>
      let x := eval vm_compute in (BlobScheduleFields_max t) in
      change (BlobScheduleFields_max t) with x
  | |- context [ProtocolProfileFields_excess_blob_gas_limit ?t] =>
      let x := eval vm_compute in (ProtocolProfileFields_excess_blob_gas_limit t) in
      change (ProtocolProfileFields_excess_blob_gas_limit t) with x
  end.

Ltac phLoopEval Hrs Hprof Hw :=
  repeat first
  [ rewrite sail_run_bind_assoc
  | rewrite sail_run_bind
  | progress cbn [SailStdpp.Prompt_monad.bind0 SailStdpp.Prompt_monad.bind returnM
      SailStdpp.Prompt_monad.returnm runPrompt fatal_error SailStdpp.Prompt_monad.exit
      read_reg SailStdpp.Prompt_monad.read_reg ssz_uint_value word_value
      Z.eqb Pos.eqb Z.of_nat Pos.of_succ_nat Pos.succ]
  | rewrite Hprof
  | progress (cbv zeta)
  | progress unfold DEFAULT_EXECUTION_PROFILE
  | rewrite phEDiv
  | progress phProfileConstants
  | progress unfold pow2, pow
  | rewrite Hw
  | match goal with |- context [if ?c then _ else _] => destruct c eqn:? end ].

Lemma phSkipLoop bytes rs (k : nat) :
  register_lookup shim_input_bytes rs = bytes ->
  forall base len (s : StatelessInputSliceFields base len) fields fuel accp,
  sliceIn bytes base len -> StatelessInputSliceFields_len s = len -> len <= fuel ->
  (List.length (sailWindow bytes base len) <= k)%nat ->
  runPrompt (_rec_decode_parent_header_fields s (Build_parent_header_field_cursor 19)
    fields fuel accp) rs true =
    (if sailSkipItems k (sailWindow bytes base len) then Success fields else Reject RlpDecode, rs).
Proof.
  intros Hrs. induction k as [|k IH]; intros base len s fields fuel accp Hin Hs Hfuel Hk;
    pose proof (sailWindowLength _ _ _ Hin) as Hwl; pose proof Hin as (Hb0 & Hl0 & Hfit0 & Hbig);
    destruct accp as [accp]; cbn [_rec_decode_parent_header_fields parent_header_field_cursor_value];
    fold (@_rec_decode_parent_header_fields);
    rewrite sail_run_bind, (sail_run_assert_true _ _ (proj2 (Z.geb_ge fuel 0) ltac:(lia))); cbv beta.
  - destruct (sailWindow bytes base len) as [|b rest] eqn:Hw; [|cbn in Hk; lia].
    cbn in Hwl. subst len. reflexivity.
  - destruct (sailWindow bytes base len) as [|b rest] eqn:Hw.
    + cbn in Hwl. subst len. reflexivity.
    + cbn [List.length] in Hwl. rewrite (proj2 (Z.eqb_neq len 0)) by lia.
      cbn [sailSkipItems].
      pose proof (phDecodeItem bytes base len s rs Hrs Hin Hs) as Hd. rewrite Hw in Hd.
      destruct (sailDecodeItem (b :: rest)) as [|l h p] eqn:Hdi.
      * rewrite sail_run_bind, Hd. reflexivity.
      * destruct Hd as [field [Hrun (Hfl & Hfc & Hfs)]].
        pose proof (phItemFacts (b :: rest) l h p ltac:(cbn [List.length]; lia) Hdi)
          as (Hh & Hp & Hhp & Hfit & Hh0).
        cbn [List.length] in Hfit.
        rewrite sail_run_bind, Hrun. cbv beta iota zeta.
        cbn [Z.eqb Pos.eqb SailStdpp.Prompt_monad.bind returnM SailStdpp.Prompt_monad.returnm
          next_parent_header_field parent_header_field_cursor_value Z.ltb Z.compare Pos.compare
          Pos.compare_cont].
        assert (Hnext : sailWindow bytes (base + StatelessInputSliceFields_len (RlpFieldRef_source field))
            (len - StatelessInputSliceFields_len (RlpFieldRef_source field)) =
            skipn (Z.to_nat (h + p)) (b :: rest)).
        { rewrite Hfs, <- Hw. apply sailWindowSuffix; auto; lia. }
        rewrite <- Hnext. unfold rlp_cursor_advance.
        apply IH.
        -- unfold sliceIn. rewrite Hfs. lia.
        -- reflexivity.
        -- rewrite Hfs. lia.
        -- rewrite Hnext. rewrite skipn_length; cbn [List.length] in *; lia.
Qed.


Definition phProfileT : Type := ltac:(let t := type of DEFAULT_EXECUTION_PROFILE in exact t).
Definition phMaxOf (v : phProfileT) : Z :=
  let '(existT _ (existT _ (existT _ (existT _ (existT _ (existT _ (existT _ (existT _ (existT _ (existT _ (existT _ (existT _ (existT _ ep))))))))))))) := v in
  BlobScheduleFields_max (ProtocolProfileFields_blob_schedule (ExecutionProfileFields_protocol ep)).
Definition phLimOf (v : phProfileT) : Z :=
  let '(existT _ (existT _ (existT _ (existT _ (existT _ (existT _ (existT _ (existT _ (existT _ (existT _ (existT _ (existT _ (existT _ ep))))))))))))) := v in
  ProtocolProfileFields_excess_blob_gas_limit (ExecutionProfileFields_protocol ep).
Lemma phMaxRs rs : register_lookup k_execution_profile rs = DEFAULT_EXECUTION_PROFILE ->
  phMaxOf (register_lookup k_execution_profile rs) = 21.
Proof. intros H. rewrite H. vm_compute. reflexivity. Qed.
Lemma phLimRs rs : register_lookup k_execution_profile rs = DEFAULT_EXECUTION_PROFILE ->
  phLimOf (register_lookup k_execution_profile rs) = 2992193280.
Proof. intros H. rewrite H. vm_compute. reflexivity. Qed.

Ltac phProfileRead Hprof :=
  match goal with |- context [register_lookup (R_ExecutionProfile k_execution_profile) ?r] =>
    let HM := fresh "HM" in let HL := fresh "HL" in
    pose proof (phMaxRs r Hprof) as HM; pose proof (phLimRs r Hprof) as HL;
    revert HM HL;
    destruct (register_lookup k_execution_profile r) as
      [? [? [? [? [? [? [? [? [? [? [? [? [? ?]]]]]]]]]]]]];
    cbn [phMaxOf phLimOf]; intros HM HL; rewrite ?HM, ?HL; clear HM HL
  end.

Ltac phFieldEval Hrs Hprof Hin Hfl Hw bytes base len rs h p field l :=
  with_strategy opaque [rlp_decode_word rlp_decode_u256 rlp_decode_uint64
      _rec_decode_parent_header_fields] (
  repeat first
  [ rewrite (phDecodeWord bytes base len rs h p field l Hrs Hin Hfl) by lia
  | rewrite (phDecodeU256 bytes base len rs h p field l Hrs Hin Hfl) by lia
  | rewrite (phDecodeUint64 bytes base len rs h p field l Hrs Hin Hfl) by lia
  | rewrite sail_run_bind
  | progress cbn [SailStdpp.Prompt_monad.bind0 SailStdpp.Prompt_monad.bind returnM
      SailStdpp.Prompt_monad.returnm runPrompt fatal_error SailStdpp.Prompt_monad.exit
      read_reg SailStdpp.Prompt_monad.read_reg ssz_uint_value word_value
      next_parent_header_field parent_header_field_cursor_value]
  | phProfileRead Hprof
  | progress cbn [String.eqb Ascii.eqb Bool.eqb andb]
  | progress (cbv zeta)
  | rewrite phEDiv
  | progress unfold pow2, pow
  | progress change (256 * 11684671 + (21 - 14) * 2 ^ 17) with 2992193280
  | rewrite Hw
  | match goal with |- context [if ?c then _ else _] => destruct c eqn:? end ]).

Ltac phValuesEq :=
  unfold sailValuesOfFields;
  cbn [ParentHeaderFields_have_base_fee ParentHeaderFields_have_blob_gas
    ParentHeaderFields_have_excess_blob_gas ParentHeaderFields_base_fee
    ParentHeaderFields_blob_gas_used ParentHeaderFields_excess_blob_gas
    sailBaseFee sailBlobGasUsed sailExcessBlobGas word_value excess_blob_gas_value];
  repeat f_equal; lia.

Lemma phFieldLoop bytes rs (c : nat) :
  register_lookup shim_input_bytes rs = bytes ->
  register_lookup k_execution_profile rs = DEFAULT_EXECUTION_PROFILE ->
  forall idx base len (s : StatelessInputSliceFields base len) fields fuel accp acc,
  (idx + c = 19)%nat -> sliceIn bytes base len -> StatelessInputSliceFields_len s = len ->
  len <= fuel -> sailValuesOfFields fields = acc ->
  match sailFieldWalk idx c (sailWindow bytes base len) acc with
  | None =>
      runPrompt (_rec_decode_parent_header_fields s
        (Build_parent_header_field_cursor (Z.of_nat idx)) fields fuel accp) rs true =
        (Reject RlpDecode, rs)
  | Some v =>
      exists fields',
        runPrompt (_rec_decode_parent_header_fields s
          (Build_parent_header_field_cursor (Z.of_nat idx)) fields fuel accp) rs true =
          (Success fields', rs) /\ sailValuesOfFields fields' = v
  end.
Proof.
  intros Hrs Hprof. induction c as [|c IH];
    intros idx base len s fields fuel accp acc Hidx Hin Hs Hfuel Hacc.
  - assert (idx = 19%nat) by lia. subst idx. cbn [sailFieldWalk]. change (Z.of_nat 19) with 19.
    rewrite (phSkipLoop bytes rs (List.length (sailWindow bytes base len)) Hrs base len s
      fields fuel accp Hin Hs Hfuel (le_n _)).
    destruct (sailSkipItems _ _); [|reflexivity].
    exists fields. split; [reflexivity|exact Hacc].
  - pose proof (sailWindowLength _ _ _ Hin) as Hwl. pose proof Hin as (Hb0 & Hl0 & Hfit0 & Hbig).
    subst acc.
    destruct accp as [accp]; cbn [_rec_decode_parent_header_fields parent_header_field_cursor_value];
      fold (@_rec_decode_parent_header_fields);
      rewrite sail_run_bind, (sail_run_assert_true _ _ (proj2 (Z.geb_ge fuel 0) ltac:(lia))); cbv beta.
    destruct (sailWindow bytes base len) as [|b rest] eqn:Hw.
    + cbn in Hwl. subst len. cbn [sailFieldWalk Z.eqb].
      exists fields. split; reflexivity.
    + cbn [List.length] in Hwl. rewrite (proj2 (Z.eqb_neq len 0)) by lia.
      pose proof (phDecodeItem bytes base len s rs Hrs Hin Hs) as Hd. rewrite Hw in Hd.
      cbn [sailFieldWalk]. unfold sailStep.
      destruct (sailDecodeItem (b :: rest)) as [|l h p] eqn:Hdi.
      * rewrite sail_run_bind, Hd. reflexivity.
      * destruct Hd as [field [Hrun (Hfl & Hfc & Hfs)]].
        pose proof (phItemFacts (b :: rest) l h p ltac:(cbn [List.length]; lia) Hdi)
          as (Hh & Hp & Hhp & Hfit & Hh0).
        cbn [List.length] in Hfit.
        assert (Hnext : sailWindow bytes (base + StatelessInputSliceFields_len (RlpFieldRef_source field))
            (len - StatelessInputSliceFields_len (RlpFieldRef_source field)) =
            skipn (Z.to_nat (h + p)) (b :: rest)).
        { rewrite Hfs, <- Hw. apply sailWindowSuffix; auto; lia. }
        destruct fields as [f1 f2 f3 f4 f5 f6 f7 f8 f9 f10].
        unfold sailFieldStep. cbv zeta.
        rewrite sail_run_bind, Hrun. cbv beta iota zeta.
        assert (Hidx18 : (idx <= 18)%nat) by lia.
        do 19 (destruct idx as [|idx];
          [ cbn [Nat.eqb orb Z.of_nat Pos.of_succ_nat Pos.succ];
            phFieldEval Hrs Hprof Hin Hfl Hw bytes base len rs h p field l;
            phBoolFacts2;
            first
            [ reflexivity
            | exfalso; lia
            | rewrite <- Hnext; unfold rlp_cursor_advance;
              match goal with |- match sailFieldWalk ?i _ _ _ with _ => _ end =>
                apply (IH i) end;
              [ lia
              | unfold sliceIn; rewrite Hfs; lia
              | reflexivity
              | rewrite Hfs; lia

              | phValuesEq ] ]
          | ]).
        lia.
Qed.



Lemma phCandidateToHdr r l h p :
  candidateDecodeItem r = candidateSuccess l h p -> sailRefHdr r = Some (l, h, p).
Proof.
  destruct r as [|prefix rest]; [discriminate|].
  unfold candidateDecodeItem, sailRefHdr, checkedPayload.
  pose proof (bv_unsigned_in_range _ prefix) as Hrange.
  repeat (cbv zeta; match goal with |- context [if ?c then _ else _] => destruct c eqn:? end; phBoolFacts2);
    intros Heq; inversion Heq; subst; phN; try reflexivity; try (exfalso; lia);
    repeat f_equal; lia.
Qed.

Lemma phHdrToCandidate r l h p :
  Z.of_nat (List.length r) < 2 ^ 31 ->
  sailRefHdr r = Some (l, h, p) -> h + p <= Z.of_nat (List.length r) ->
  candidateDecodeItem r = candidateSuccess l h p.
Proof.
  intros Hlen Hh Hfit. pose proof (sailDecodeItemHdr r Hlen) as Hd.
  rewrite Hh, (proj2 (Z.leb_le _ _) Hfit) in Hd. unfold sailDecodeItem in Hd.
  destruct (candidateDecodeItem r) as [|l' h' p']; [discriminate|].
  destruct (h' + p' <=? Z.of_nat (List.length r)); congruence.
Qed.

Definition phInstalled (bytes : list byte) : regstate :=
  register_set shim_input_bytes bytes
    (register_set k_execution_profile DEFAULT_EXECUTION_PROFILE
      (register_set shim_input_bytes [] init_regstate)).

Lemma phInit bytes :
  runPrompt (initializedInput bytes) init_regstate true = (Success tt, phInstalled bytes).
Proof. reflexivity. Qed.

Lemma phInstalledBytes bytes : register_lookup shim_input_bytes (phInstalled bytes) = bytes.
Proof. unfold phInstalled. apply register_lookup_set. Qed.

Lemma phInstalledProfile bytes :
  register_lookup k_execution_profile (phInstalled bytes) = DEFAULT_EXECUTION_PROFILE.
Proof. unfold phInstalled. rewrite inputInstallPreservesProfile. apply register_lookup_set. Qed.

Lemma phValid bytes base len :
  0 <= base -> 0 <= len -> base + len <= Z.of_nat (List.length bytes) ->
  Z.of_nat (List.length bytes) < 2 ^ 31 -> validInputSlice bytes base len = true.
Proof.
  intros. unfold validInputSlice, stateless_input_region_bound.
  repeat (apply andb_true_iff; split); apply Z.leb_le; lia.
Qed.

Ltac phTopEval :=
  repeat first
  [ rewrite sail_run_bind_assoc
  | rewrite sail_run_bind
  | progress cbn [SailStdpp.Prompt_monad.bind0 SailStdpp.Prompt_monad.bind returnM
      SailStdpp.Prompt_monad.returnm runPrompt fatal_error SailStdpp.Prompt_monad.exit
      source_pointer_value RlpFieldRef_is_list String.eqb Ascii.eqb Bool.eqb andb fst
      parent_header_field_cursor_value]
  | progress (cbv zeta) ].

Theorem sailParentHeaderModel_holds : SailParentHeaderModel.
Proof.
  intros bytes _ Hlen.
  assert (Hin : sliceIn bytes 0 (Z.of_nat (List.length bytes))) by (unfold sliceIn; lia).
  assert (Hwin : sailWindow bytes 0 (Z.of_nat (List.length bytes)) = bytes).
  { unfold sailWindow. rewrite Nat2Z.id. cbn [Z.to_nat skipn]. apply firstn_all. }
  unfold sailParentHeaderRun, runRlpNodeCursor, ZesuSsz.Compliance.SailRun.runDecoder.
  rewrite (phValid bytes 0 (Z.of_nat (List.length bytes))) by lia.
  cbn [SailStdpp.Prompt_monad.bind0]. rewrite sail_run_bind, phInit. cbv beta iota.
  pose proof (phInstalledBytes bytes) as Hrs. pose proof (phInstalledProfile bytes) as Hprof.
  unfold rlp_node_cursor.
  change (StatelessInputSliceFields_len (parentHeaderSailNode bytes)) with (Z.of_nat (List.length bytes)).
  unfold sailPureParentHeader.
  destruct (Z.eqb_spec (Z.of_nat (List.length bytes)) 0) as [Hn0|Hn0].
  { destruct bytes; [|cbn in Hn0; lia]. reflexivity. }
  unfold rlp_single_ref. rewrite (proj2 (Z.eqb_neq _ 0) Hn0).
  rewrite sail_run_bind, sail_run_bind_assoc, sail_run_bind.
  rewrite (phRefHdr bytes 0 (Z.of_nat (List.length bytes)) (parentHeaderSailNode bytes)
    (phInstalled bytes) Hrs Hin eq_refl), Hwin.
  destruct (sailRefHdr bytes) as [[[l h] p]|] eqn:Hh.
  2: { destruct (candidateDecodeItem bytes) as [|l' h' p'] eqn:Hc; [reflexivity|].
       apply phCandidateToHdr in Hc. congruence. }
  pose proof (sailRefHdrNonneg _ _ _ _ Hh) as (Hh9 & Hp0 & Hhp & _).
  cbn [hdrOutcome]. phTopEval.
  destruct (Z.eqb_spec (h + p) (Z.of_nat (List.length bytes))) as [Hfit|Hfit].
  2: { rewrite (proj2 (Z.eqb_neq p (Z.of_nat (List.length bytes) - h))) by lia.
       rewrite andb_false_r. phTopEval.
       destruct (candidateDecodeItem bytes) as [|l' h' p'] eqn:Hc; [reflexivity|].
       pose proof (phCandidateToHdr _ _ _ _ Hc) as Hc'. rewrite Hh in Hc'. inversion Hc'; subst.
       first [destruct l | destruct l']; [|reflexivity].
       match goal with |- context [?a =? Z.of_nat (List.length bytes)] =>
         destruct (Z.eqb_spec a (Z.of_nat (List.length bytes))); [lia|reflexivity] end. }
  rewrite (proj2 (Z.leb_le h (Z.of_nat (List.length bytes)))) by lia.
  rewrite (proj2 (Z.eqb_eq p (Z.of_nat (List.length bytes) - h))) by lia.
  rewrite (phHdrToCandidate bytes l h p Hlen Hh) by lia.
  rewrite Hfit, Z.eqb_refl.
  phTopEval. unfold rlp_decode_list. cbn [RlpFieldRef_is_list].
  destruct l; [|phTopEval; reflexivity].
  phTopEval.
  unfold runParentHeaderFields. cbn [parent_header_field_cursor_value].
  change ((0 <=? 0) && (0 <=? 19)) with true. cbv iota.
  unfold ZesuSsz.Compliance.SailRun.runDecoder.
  rewrite (phValid bytes (0 + (Z.of_nat (List.length bytes) - p)) p) by lia.
  cbn [SailStdpp.Prompt_monad.bind0]. rewrite sail_run_bind, phInit. cbv beta iota.
  unfold decode_parent_header_fields. cbn [parent_header_field_cursor_value].
  assert (Hin2 : sliceIn bytes (0 + (Z.of_nat (List.length bytes) - p)) p) by (unfold sliceIn; lia).
  assert (Hw2 : sailWindow bytes (0 + (Z.of_nat (List.length bytes) - p)) p = itemPayload bytes h p).
  { unfold sailWindow, itemPayload. f_equal. f_equal. lia. }
  match goal with |- context [_rec_decode_parent_header_fields ?s _ _ ?fuel ?acc] =>
    pose proof (phFieldLoop bytes (phInstalled bytes) 19 Hrs Hprof 0 _ _ s emptyParentFields
      fuel acc sailNoValues eq_refl Hin2 eq_refl ltac:(cbn; lia) eq_refl) as Hloop end.
  rewrite Hw2 in Hloop. change (Z.of_nat 0) with 0 in Hloop.
  change (List.length parentHeaderFieldSchedule) with 19%nat.
  destruct (sailFieldWalk 0 19 (itemPayload bytes h p) sailNoValues).
  - destruct Hloop as [fields [Hrun Hv]]. exists fields. rewrite Hrun. split; [reflexivity|exact Hv].
  - rewrite Hloop. reflexivity.
Qed.

Theorem candidateParentHeader_sail_from_cover :
  KnownBugTriggersCoverDivergences ->
  forall bytes : list byte,
    headerFits bytes -> Z.of_nat (List.length bytes) < 2 ^ 31 ->
    (forall bug, List.In bug knownBugs -> parentHeaderBugTrigger bug bytes = false) ->
    parentHeaderSailAgrees bytes.
Proof.
  intros Hcover. exact (candidateParentHeader_sail_from_model_and_cover sailParentHeaderModel_holds Hcover).
Qed.

Print Assumptions sailParentHeaderModel_holds.
Print Assumptions candidateParentHeader_sail_from_cover.
