From Coq Require Import Lia Lists.List ZArith.ZArith.
Require Import isla.opsem.

Import ListNotations.
Open Scope Z_scope.

Definition islaMemoryRange (address : Z) (length : nat) : Prop :=
  0 <= address /\ address + Z.of_nat length <= 2 ^ 64.

Definition islaMemoryRangesDisjoint
    (first : Z) (firstLength : nat)
    (second : Z) (secondLength : nat) : Prop :=
  first + Z.of_nat firstLength <= second \/
  second + Z.of_nat secondLength <= first.

Lemma islaMemoryBvSucc address :
  islaMemoryRange address 1 ->
  bv_add_Z (Z_to_bv 64 address) 1 = Z_to_bv 64 (address + 1).
Proof.
  intros Hrange. unfold islaMemoryRange in Hrange.
  destruct Hrange as [Hlower Hupper]. apply bv_eq.
  rewrite bv_add_Z_unsigned !Z_to_bv_unsigned.
  bv_wrap_simplify_solve.
Qed.

Lemma write_mem_list_lookup_outside mem address bytes key :
  islaMemoryRange address (length bytes) ->
  0 <= key < 2 ^ 64 ->
  (key < address \/ address + Z.of_nat (length bytes) <= key) ->
  write_mem_list mem (Z_to_bv 64 address) bytes !! Z_to_bv 64 key =
    mem !! Z_to_bv 64 key.
Proof.
  revert mem address key.
  induction bytes as [|byte bytes IH]; intros mem address key Hrange Hkey Houtside.
  - reflexivity.
  - cbn in Hrange |- *.
    rewrite islaMemoryBvSucc; [|unfold islaMemoryRange in *; cbn; lia].
    rewrite IH.
    + rewrite lookup_insert_ne; [reflexivity |].
      apply bv_neq. rewrite !Z_to_bv_unsigned.
      have Haddress : (0 <= address < bv_modulus 64)%Z.
      { unfold islaMemoryRange, bv_modulus in *; cbn in *; lia. }
      have Hkey' : (0 <= key < bv_modulus 64)%Z.
      { unfold bv_modulus; exact Hkey. }
      rewrite (bv_wrap_small 64 address Haddress)
        (bv_wrap_small 64 key Hkey').
      unfold islaMemoryRange in *; cbn in *; lia.
    + unfold islaMemoryRange in *. cbn in *. lia.
    + exact Hkey.
    + unfold islaMemoryRange in *. cbn in *. lia.
Qed.

Lemma read_mem_list_written mem address bytes :
  islaMemoryRange address (length bytes) ->
  read_mem_list (write_mem_list mem (Z_to_bv 64 address) bytes)
    address (N.of_nat (length bytes)) = Some bytes.
Proof.
  intros Hrange. unfold read_mem_list.
  apply mapM_Some_2.
  revert mem address Hrange.
  induction bytes as [|byte bytes IH]; intros mem address Hrange.
  - cbn. rewrite seqZ_nil; last lia.
    exact (@Forall2_nil_2 Z (bv 8) _).
  - rewrite seqZ_cons; [|cbn; lia].
    cbn [write_mem_list].
    rewrite islaMemoryBvSucc; [|unfold islaMemoryRange in *; cbn in *; lia].
    apply Forall2_cons_2.
    + apply bind_Some. exists (Z_to_bv 64 address). split.
      * apply Z_to_bv_checked_Some. rewrite Z_to_bv_unsigned.
        rewrite bv_wrap_small; unfold islaMemoryRange, bv_modulus in *; cbn in *; lia.
      * rewrite (write_mem_list_lookup_outside
          (<[Z_to_bv 64 address := byte]> mem) (address + 1) bytes address).
        -- apply lookup_insert.
        -- unfold islaMemoryRange in *; cbn in *; lia.
        -- unfold islaMemoryRange in *; cbn in *; lia.
        -- left. lia.
    + replace (Z.succ address) with (address + 1) by lia.
      replace (Z.pred (Z.of_N (N.of_nat (length (byte :: bytes))))) with
        (Z.of_N (N.of_nat (length bytes))) by (cbn; lia).
      apply IH. unfold islaMemoryRange in *; cbn in *; lia.
Qed.

Lemma read_mem_list_append mem address firstLength secondLength first second :
  read_mem_list mem address (N.of_nat firstLength) = Some first ->
  read_mem_list mem (address + Z.of_nat firstLength)
    (N.of_nat secondLength) = Some second ->
  read_mem_list mem address (N.of_nat (firstLength + secondLength)) =
    Some (first ++ second).
Proof.
  intros Hfirst Hsecond. unfold read_mem_list in *.
  apply mapM_Some_1 in Hfirst. apply mapM_Some_1 in Hsecond.
  replace (Z.of_N (N.of_nat firstLength)) with (Z.of_nat firstLength)
    in Hfirst by lia.
  replace (Z.of_N (N.of_nat secondLength)) with (Z.of_nat secondLength)
    in Hsecond by lia.
  apply mapM_Some_2.
  replace (Z.of_N (N.of_nat (firstLength + secondLength))) with
    (Z.of_nat (firstLength + secondLength)) by lia.
  rewrite Nat2Z.inj_add seqZ_app; try lia.
  apply Forall2_app; assumption.
Qed.

Lemma read_mem_list_split mem address firstLength secondLength bytes :
  read_mem_list mem address (N.of_nat (firstLength + secondLength)) =
    Some bytes ->
  exists first second,
    bytes = first ++ second /\
    length first = firstLength /\
    length second = secondLength /\
    read_mem_list mem address (N.of_nat firstLength) = Some first /\
    read_mem_list mem (address + Z.of_nat firstLength)
      (N.of_nat secondLength) = Some second.
Proof.
  intros Hread. unfold read_mem_list in *.
  apply mapM_Some_1 in Hread.
  replace (Z.of_N (N.of_nat (firstLength + secondLength))) with
    (Z.of_nat (firstLength + secondLength)) in Hread by lia.
  rewrite Nat2Z.inj_add seqZ_app in Hread; try lia.
  apply Forall2_app_inv_l in Hread.
  destruct Hread as (first & second & Hfirst & Hsecond & ->).
  exists first, second. repeat split.
  - by eapply Forall2_length in Hfirst; rewrite length_seqZ Nat2Z.id in Hfirst.
  - by eapply Forall2_length in Hsecond; rewrite length_seqZ Nat2Z.id in Hsecond.
  - apply mapM_Some_2.
    replace (Z.of_N (N.of_nat firstLength)) with (Z.of_nat firstLength) by lia.
    exact Hfirst.
  - apply mapM_Some_2.
    replace (Z.of_N (N.of_nat secondLength)) with (Z.of_nat secondLength) by lia.
    exact Hsecond.
Qed.

Lemma mapM_ext_in {A B} (f g : A -> option B) xs :
  (forall x, In x xs -> f x = g x) ->
  mapM f xs = mapM g xs.
Proof.
  intros Hequal. induction xs as [|x xs IH]; first reflexivity.
  cbn. rewrite Hequal; [|by left].
  destruct (g x); cbn; last reflexivity.
  rewrite IH; first reflexivity.
  intros y Hy. apply Hequal. by right.
Qed.

Lemma read_mem_list_write_mem_list_disjoint_eq mem writeAddress bytes
    readAddress readLength :
  islaMemoryRange writeAddress (length bytes) ->
  islaMemoryRangesDisjoint writeAddress (length bytes)
    readAddress readLength ->
  read_mem_list (write_mem_list mem (Z_to_bv 64 writeAddress) bytes)
    readAddress (N.of_nat readLength) =
  read_mem_list mem readAddress (N.of_nat readLength).
Proof.
  intros HwriteRange Hdisjoint. unfold read_mem_list.
  apply mapM_ext_in. intros location Hlocation.
  have HlocationRange :
      readAddress <= location < readAddress + Z.of_nat readLength.
  { apply elem_of_list_In in Hlocation. apply elem_of_seqZ in Hlocation.
    replace (Z.of_N (N.of_nat readLength)) with
      (Z.of_nat readLength) in Hlocation by lia.
    lia. }
  destruct (Z_to_bv_checked 64 location) as [key|] eqn:Hkey; cbn;
    [|reflexivity].
  apply Z_to_bv_checked_Some in Hkey. subst location.
  have HkeyOutside :
      bv_unsigned key < writeAddress \/
      writeAddress + Z.of_nat (length bytes) <= bv_unsigned key.
  { unfold islaMemoryRangesDisjoint in Hdisjoint.
    destruct Hdisjoint; [right | left]; unfold islaMemoryRange in *; lia. }
  have Houtside := write_mem_list_lookup_outside mem writeAddress bytes
    (bv_unsigned key) HwriteRange (bv_unsigned_in_range 64 key) HkeyOutside.
  by rewrite Z_to_bv_bv_unsigned in Houtside.
Qed.

Lemma read_mem_list_write_mem_list_disjoint mem writeAddress bytes
    readAddress readLength result :
  islaMemoryRange writeAddress (length bytes) ->
  islaMemoryRangesDisjoint writeAddress (length bytes)
    readAddress readLength ->
  read_mem_list mem readAddress (N.of_nat readLength) = Some result ->
  read_mem_list (write_mem_list mem (Z_to_bv 64 writeAddress) bytes)
    readAddress (N.of_nat readLength) = Some result.
Proof.
  intros HwriteRange Hdisjoint Hread.
  rewrite read_mem_list_write_mem_list_disjoint_eq; try assumption.
Qed.

Lemma write_mem_list_dom mem address bytes :
  islaMemoryRange address (length bytes) ->
  (forall location,
    address <= location < address + Z.of_nat (length bytes) ->
    is_Some (mem !! Z_to_bv 64 location)) ->
  dom (write_mem_list mem (Z_to_bv 64 address) bytes) = dom mem.
Proof.
  revert mem address.
  induction bytes as [|byte bytes IH]; intros mem address Hrange Hbacked.
  - reflexivity.
  - cbn in Hrange |- *.
    rewrite islaMemoryBvSucc; [|unfold islaMemoryRange in *; cbn in *; lia].
    rewrite IH.
    + rewrite dom_insert_L.
      have Hin : Z_to_bv 64 address ∈ dom mem.
      { apply elem_of_dom. apply Hbacked. cbn. lia. }
      set_solver.
    + unfold islaMemoryRange in *; cbn in *; lia.
    + intros location Hlocation.
      rewrite lookup_insert_ne.
      * apply Hbacked. cbn in *. lia.
      * apply bv_neq. rewrite !Z_to_bv_unsigned.
        rewrite !bv_wrap_small; unfold islaMemoryRange, bv_modulus in *; cbn in *; lia.
Qed.

Lemma read_mem_list_to_read_mem mem address length bytes :
  read_mem_list mem address length = Some bytes ->
  read_mem mem address length =
    Some (bv_to_bvn
      (Z_to_bv (8 * length) (little_endian_to_bv 8 bytes))).
Proof. intros Hread. unfold read_mem. by rewrite Hread. Qed.

Lemma read_mem_to_read_mem_list mem address length value :
  read_mem mem address length = Some value ->
  exists bytes,
    read_mem_list mem address length = Some bytes /\
    value = bv_to_bvn
      (Z_to_bv (8 * length) (little_endian_to_bv 8 bytes)).
Proof.
  unfold read_mem. destruct (read_mem_list mem address length) as [bytes|];
    cbn; [intros Hequal; inversion Hequal; subst; eauto | congruence].
Qed.

Lemma read_mem_list_write_mem mem address length value :
  islaMemoryRange address (N.to_nat length) ->
  read_mem_list (write_mem length mem (Z_to_bv 64 address) value)
    address length =
    Some (bv_to_little_endian (N.to_nat length) 8 value).
Proof.
  intros Hrange. unfold write_mem.
  replace length with (N.of_nat (N.to_nat length)) at 2 by lia.
  replace (N.of_nat (N.to_nat length)) with
    (N.of_nat (List.length (bv_to_little_endian (N.to_nat length) 8 value))).
  2: { rewrite length_bv_to_little_endian; lia. }
  apply read_mem_list_written.
  rewrite length_bv_to_little_endian; [|lia].
  rewrite Nat2Z.id. exact Hrange.
Qed.

Lemma read_mem_write_mem mem address length value :
  islaMemoryRange address (N.to_nat length) ->
  read_mem (write_mem length mem (Z_to_bv 64 address) value)
    address length = Some (bv_to_bvn (Z_to_bv (8 * length) value)).
Proof.
  intros Hrange. unfold read_mem.
  rewrite read_mem_list_write_mem; [|exact Hrange]. cbn.
  f_equal. apply (proj2 (bvn_eq _ _)). split; first reflexivity.
  cbn.
  rewrite little_endian_to_bv_to_little_endian; [|lia].
  unfold bvn_unsigned; cbn. rewrite !Z_to_bv_unsigned.
  unfold bv_wrap, bv_modulus.
  replace (Z.of_N (8 * length)) with
    (Z.of_nat (N.to_nat length) * Z.of_N 8)%Z by lia.
  cbn. rewrite Z.mod_mod; [reflexivity | apply Z.pow_nonzero; lia].
Qed.

Lemma read_mem_list_write_mem_disjoint mem writeAddress length value
    readAddress readLength result :
  islaMemoryRange writeAddress (N.to_nat length) ->
  islaMemoryRangesDisjoint writeAddress (N.to_nat length)
    readAddress readLength ->
  read_mem_list mem readAddress (N.of_nat readLength) = Some result ->
  read_mem_list (write_mem length mem (Z_to_bv 64 writeAddress) value)
    readAddress (N.of_nat readLength) = Some result.
Proof.
  unfold write_mem. intros Hwrite Hdisjoint Hresult.
  have Hlength : List.length
      (bv_to_little_endian (N.to_nat length) 8 value) = N.to_nat length.
  { rewrite length_bv_to_little_endian; [rewrite Nat2Z.id; reflexivity | lia]. }
  eapply read_mem_list_write_mem_list_disjoint.
  - rewrite Hlength. exact Hwrite.
  - rewrite Hlength. exact Hdisjoint.
  - exact Hresult.
Qed.

Lemma read_mem_list_write_mem_disjoint_eq mem writeAddress length value
    readAddress readLength :
  islaMemoryRange writeAddress (N.to_nat length) ->
  islaMemoryRangesDisjoint writeAddress (N.to_nat length)
    readAddress readLength ->
  read_mem_list (write_mem length mem (Z_to_bv 64 writeAddress) value)
    readAddress (N.of_nat readLength) =
  read_mem_list mem readAddress (N.of_nat readLength).
Proof.
  unfold write_mem. intros Hwrite Hdisjoint.
  have Hlength : List.length
      (bv_to_little_endian (N.to_nat length) 8 value) = N.to_nat length.
  { rewrite length_bv_to_little_endian; [rewrite Nat2Z.id; reflexivity | lia]. }
  apply read_mem_list_write_mem_list_disjoint_eq.
  - rewrite Hlength. exact Hwrite.
  - rewrite Hlength. exact Hdisjoint.
Qed.

Lemma read_mem_write_mem_disjoint mem writeAddress writeLength value
    readAddress readLength result :
  islaMemoryRange writeAddress (N.to_nat writeLength) ->
  islaMemoryRangesDisjoint writeAddress (N.to_nat writeLength)
    readAddress (N.to_nat readLength) ->
  read_mem mem readAddress readLength = Some result ->
  read_mem (write_mem writeLength mem (Z_to_bv 64 writeAddress) value)
    readAddress readLength = Some result.
Proof.
  intros Hwrite Hdisjoint Hresult.
  apply read_mem_to_read_mem_list in Hresult as
    (bytes & Hbytes & ->).
  apply read_mem_list_to_read_mem.
  replace readLength with (N.of_nat (N.to_nat readLength)) in Hbytes |- * by lia.
  eapply read_mem_list_write_mem_disjoint; eassumption.
Qed.

Lemma read_mem_write_mem_disjoint_eq mem writeAddress writeLength value
    readAddress readLength :
  islaMemoryRange writeAddress (N.to_nat writeLength) ->
  islaMemoryRangesDisjoint writeAddress (N.to_nat writeLength)
    readAddress (N.to_nat readLength) ->
  read_mem (write_mem writeLength mem (Z_to_bv 64 writeAddress) value)
    readAddress readLength = read_mem mem readAddress readLength.
Proof.
  intros Hwrite Hdisjoint.
  replace readLength with (N.of_nat (N.to_nat readLength)) by lia.
  unfold read_mem.
  f_equal. apply read_mem_list_write_mem_disjoint_eq; assumption.
Qed.

Lemma write_mem_dom mem address length value :
  islaMemoryRange address (N.to_nat length) ->
  (forall location,
    address <= location < address + Z.of_N length ->
    is_Some (mem !! Z_to_bv 64 location)) ->
  dom (write_mem length mem (Z_to_bv 64 address) value) = dom mem.
Proof.
  intros Hrange Hbacked. unfold write_mem.
  have Hlength : List.length
      (bv_to_little_endian (N.to_nat length) 8 value) = N.to_nat length.
  { rewrite length_bv_to_little_endian; [rewrite Nat2Z.id; reflexivity | lia]. }
  apply write_mem_list_dom.
  - rewrite Hlength. exact Hrange.
  - intros location Hlocation. apply Hbacked.
    rewrite Hlength in Hlocation. lia.
Qed.

Print Assumptions islaMemoryBvSucc.
Print Assumptions write_mem_list_lookup_outside.
Print Assumptions read_mem_list_written.
Print Assumptions read_mem_list_append.
Print Assumptions read_mem_list_split.
Print Assumptions mapM_ext_in.
Print Assumptions read_mem_list_write_mem_list_disjoint_eq.
Print Assumptions read_mem_list_write_mem_list_disjoint.
Print Assumptions write_mem_list_dom.
Print Assumptions read_mem_list_to_read_mem.
Print Assumptions read_mem_to_read_mem_list.
Print Assumptions read_mem_list_write_mem.
Print Assumptions read_mem_write_mem.
Print Assumptions read_mem_list_write_mem_disjoint.
Print Assumptions read_mem_list_write_mem_disjoint_eq.
Print Assumptions read_mem_write_mem_disjoint.
Print Assumptions read_mem_write_mem_disjoint_eq.
Print Assumptions write_mem_dom.
