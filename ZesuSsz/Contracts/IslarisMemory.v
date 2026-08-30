From Coq Require Import Lists.List ZArith.ZArith.
Require Import isla.riscv64.riscv64.
Require Export ZesuSsz.Contracts.IslarisEndian.

Import ListNotations.

Definition bytes_of_u64s (values : list (bv 64)) : list (bv 8) :=
  values ≫= fun value => bv_to_little_endian 8 8 (bv_unsigned value).

Definition u64s_of_bytes (count : nat) (values : list (bv 8)) :
    list (bv 64) :=
  (fun bytes => Z_to_bv 64 (little_endian_to_bv 8 bytes))
    <$> reshape (replicate count 8%nat) values.

Lemma reshape_8_lengths count (values : list (bv 8)) :
  length values = (count * 8)%nat ->
  Forall (fun bytes => length bytes = 8%nat)
    (reshape (replicate count 8%nat) values).
Proof.
  revert values. induction count as [|count IH]; intros values Hlength.
  - cbn. constructor.
  - cbn. constructor.
    + rewrite length_take. lia.
    + apply IH. rewrite length_drop. lia.
Qed.

Lemma u64_bytes_roundtrip (values : list (bv 8)) :
  length values = 8%nat ->
  bv_to_little_endian 8 8
    (bv_unsigned (Z_to_bv 64 (little_endian_to_bv 8 values))) = values.
Proof.
  intros Hlength.
  have Hbound :
    (0 <= little_endian_to_bv 8 values < bv_modulus 64)%Z.
  { pose proof (little_endian_to_bv_bound 8 values).
    unfold bv_modulus. rewrite Hlength in H. cbn in H |-; lia. }
  rewrite Z_to_bv_small; [apply bv_to_little_endian_to_bv; lia | done].
Qed.

Lemma bytes_of_u64s_map_chunks (chunks : list (list (bv 8))) :
  Forall (fun bytes => length bytes = 8%nat) chunks ->
  bytes_of_u64s
    ((fun bytes => Z_to_bv 64 (little_endian_to_bv 8 bytes)) <$> chunks) =
  mjoin chunks.
Proof.
  intros Hchunks. induction Hchunks as [|chunk chunks Hlength Hchunks IH].
  - reflexivity.
  - unfold bytes_of_u64s in IH |- *. cbn.
    rewrite (u64_bytes_roundtrip chunk Hlength) IH. reflexivity.
Qed.

Lemma bytes_of_u64s_of_bytes count (values : list (bv 8)) :
  length values = (count * 8)%nat ->
  bytes_of_u64s (u64s_of_bytes count values) = values.
Proof.
  intros Hlength. rewrite /u64s_of_bytes.
  rewrite bytes_of_u64s_map_chunks; [|by apply reshape_8_lengths].
  apply join_reshape. rewrite sum_list_replicate. symmetry. exact Hlength.
Qed.

Section array_regions.
  Context `{!islaG Sigma}.

  Lemma mem_mapsto_byte_array_to_mapsto (a : Z) q
      (values : list (bv 8)) :
    a ↦ₘ{q}∗ values -∗
    a ↦ₘ{q}
      (Z_to_bv (Z.to_N (Z.of_nat (length values)) * 8)
        (little_endian_to_bv 8 values)).
  Proof.
    rewrite mem_mapsto_array_eq mem_mapsto_eq /mem_mapsto_array_def
      /mem_mapsto_def.
    iIntros "Harray".
    iDestruct "Harray" as (len Hlen Hrange) "Harray".
    have Hlen' : len = 1%N by nia. subst len.
    iExists (length values). iSplit; [iPureIntro; lia |].
    iSplit; [iPureIntro; nia |].
    have Hbound :
      (0 <= little_endian_to_bv 8 values <
        bv_modulus (Z.to_N (Z.of_nat (length values)) * 8))%Z.
    { pose proof (little_endian_to_bv_bound 8 values).
      unfold bv_modulus. rewrite N2Z.inj_mul Z2N.id; lia. }
    have Hroundtrip :
      bv_to_little_endian (length values) 8
        (bv_unsigned
          (Z_to_bv (Z.to_N (Z.of_nat (length values)) * 8)
            (little_endian_to_bv 8 values))) = values.
    { rewrite Z_to_bv_small.
      - apply bv_to_little_endian_to_bv. lia.
      - exact Hbound. }
    rewrite Hroundtrip.
    iApply (big_sepL_impl with "Harray").
    iIntros "!>" (index value Hlookup) "Hvalue".
    rewrite mem_mapsto_eq /mem_mapsto_def.
    iDestruct "Hvalue" as (byteLen HbyteLen HbyteRange) "Hvalue".
    have HbyteLen' : byteLen = 1%nat by nia. subst byteLen.
    iEval (cbn; rewrite Z.mul_1_r) in "Hvalue".
    iDestruct "Hvalue" as "[Hvalue _]".
    rewrite /= Z.add_0_r -(bv_wrap_land 8) bv_wrap_small
      ?Z_to_bv_bv_unsigned; [iExact "Hvalue" | apply bv_unsigned_in_range].
  Qed.

  Lemma mem_mapsto_mapsto_to_byte_array (a : Z) q (value : bv 64) :
    a ↦ₘ{q} value -∗
    a ↦ₘ{q}∗ bv_to_little_endian 8 8 (bv_unsigned value).
  Proof.
    rewrite mem_mapsto_eq mem_mapsto_array_eq /mem_mapsto_def
      /mem_mapsto_array_def.
    iIntros "Hvalue".
    iDestruct "Hvalue" as (len Hlen Hrange) "Hvalue".
    have Hlen' : len = 8%nat by nia. subst len.
    iExists 1%N. iSplit; [done |]. iSplit.
    { iPureIntro. rewrite length_bv_to_little_endian; [nia | nia]. }
    iApply (big_sepL_impl with "Hvalue").
    iIntros "!>" (index byte Hlookup) "Hbyte".
    replace (a + Z.of_nat index * Z.of_N 1)%Z with
      (a + Z.of_nat index)%Z by (cbn; lia).
    iApply mem_mapsto_byte_to_mapsto. iExact "Hbyte".
  Qed.

  Lemma mem_mapsto_array_singleton n (a : Z) q (value : bv n) :
    a ↦ₘ{q}∗ [value] ⊣⊢ a ↦ₘ{q} value.
  Proof.
    rewrite mem_mapsto_array_eq /mem_mapsto_array_def. iSplit.
    - iIntros "Harray".
      iDestruct "Harray" as (len Hlen Hrange) "[Hvalue _]".
      iEval (cbn; rewrite Z.add_0_r) in "Hvalue".
      iExact "Hvalue".
    - rewrite mem_mapsto_eq /mem_mapsto_def.
      iIntros "Hvalue".
      iDestruct "Hvalue" as (len Hlen Hrange) "Hvalue".
      iExists (N.of_nat len). iSplit; [iPureIntro; lia |].
      iSplit; [iPureIntro; cbn; nia |].
      rewrite big_sepL_singleton /= Z.add_0_r.
      iExists len. iSplit; [done |]. iSplit; [iPureIntro; nia |].
      iExact "Hvalue".
  Qed.

  Lemma mem_mapsto_uninit_to_byte_array (a n : Z) q :
    a ↦ₘ{q}? n -∗
    ∃ values : list (bv 8),
      ⌜Z.of_nat (length values) = n⌝ ∗ a ↦ₘ{q}∗ values.
  Proof.
    rewrite mem_mapsto_uninit_eq mem_mapsto_array_eq.
    iIntros "Hmemory".
    iDestruct "Hmemory" as (length Hlength Hrange) "Hbytes".
    iDestruct (big_sepL_exist with "Hbytes") as (values Hvalues) "Hbytes".
    rewrite length_replicate in Hvalues.
    subst length.
    iExists values. iSplit; [done |].
    iExists 1%N. iSplit; [done |]. iSplit.
    { iPureIntro. lia. }
    iApply (big_sepL_impl' with "Hbytes").
    { by rewrite length_replicate. }
    iIntros "!>" (index ? ? ??) "[%byte [% Hbyte]]".
    simplify_eq.
    rewrite mem_mapsto_eq.
    iExists 1%nat. iSplit; [done |]. iSplit.
    { iPureIntro. have := lookup_lt_Some values index x2 H0. lia. }
    rewrite /= Z.add_0_r.
    replace (Z_to_bv 8 (Z.land (bv_unsigned x2) (Z.ones 8))) with x2
      by bv_solve.
    rewrite Z.mul_1_r. iFrame.
  Qed.

  Lemma mem_mapsto_array_app n (a : Z) q
      (left right : list (bv n)) :
    a ↦ₘ{q}∗ (left ++ right) -∗
    a ↦ₘ{q}∗ left ∗
    (a + Z.of_N (n `div` 8) * length left) ↦ₘ{q}∗ right.
  Proof.
    rewrite !mem_mapsto_array_eq /mem_mapsto_array_def.
    iIntros "Harray".
    iDestruct "Harray" as (len Hn Hrange) "Harray".
    rewrite big_sepL_app.
    iDestruct "Harray" as "[Hleft Hright]".
    have Hlen : Z.of_N len = Z.of_N (n `div` 8) by nia.
    iSplitL "Hleft".
    - iExists len. iFrame. iPureIntro.
      split; [done |]. rewrite length_app in Hrange. lia.
    - iExists len. iSplit; [done |]. iSplit.
      { iPureIntro. rewrite length_app in Hrange. lia. }
      iApply (big_sepL_impl with "Hright").
      iIntros "!>" (k value Hlookup) "Hvalue".
      have Haddress :
        (a + Z.of_nat (length left + k) * Z.of_N len)%Z =
        (a + Z.of_N (n `div` 8) * Z.of_nat (length left) +
         Z.of_nat k * Z.of_N len)%Z.
      { rewrite Nat2Z.inj_add. lia. }
      iEval (rewrite Haddress) in "Hvalue".
      iExact "Hvalue".
  Qed.

  Lemma mem_mapsto_array_app_combine n (a : Z) q
      (left right : list (bv n)) :
    a ↦ₘ{q}∗ left -∗
    (a + Z.of_N (n `div` 8) * length left) ↦ₘ{q}∗ right -∗
    a ↦ₘ{q}∗ (left ++ right).
  Proof.
    rewrite !mem_mapsto_array_eq /mem_mapsto_array_def.
    iIntros "Hleft Hright".
    iDestruct "Hleft" as (len Hn HleftRange) "Hleft".
    iDestruct "Hright" as (len' Hn' HrightRange) "Hright".
    have Hlen : len = len' by nia. subst len'.
    iExists len. iSplit; [done |]. iSplit.
    { iPureIntro. rewrite length_app. nia. }
    rewrite big_sepL_app. iFrame "Hleft".
    iApply (big_sepL_impl with "Hright").
    iIntros "!>" (k value Hlookup) "Hvalue".
    have Haddress :
      (a + Z.of_nat (length left + k) * Z.of_N len =
       a + Z.of_N (n `div` 8) * Z.of_nat (length left) +
         Z.of_nat k * Z.of_N len)%Z.
    { rewrite Nat2Z.inj_add. nia. }
    iEval (rewrite Haddress).
    iExact "Hvalue".
  Qed.

  Lemma mem_mapsto_array_app_combine_at n (a : Z) q
      (left right : list (bv n)) (count : nat) :
    length left = count ->
    a ↦ₘ{q}∗ left -∗
    (a + Z.of_N (n `div` 8) * count) ↦ₘ{q}∗ right -∗
    a ↦ₘ{q}∗ (left ++ right).
  Proof.
    iIntros (Hcount) "Hleft Hright".
    iApply (mem_mapsto_array_app_combine n a q left right with "Hleft").
    rewrite Hcount. iExact "Hright".
  Qed.

  Lemma mem_mapsto_u64_array_to_bytes (a : Z) q
      (values : list (bv 64)) :
    a ↦ₘ{q}∗ values -∗ a ↦ₘ{q}∗ bytes_of_u64s values.
  Proof.
    iInduction values as [|value values] "IH" forall (a).
    - rewrite /bytes_of_u64s /= !mem_mapsto_array_eq
        /mem_mapsto_array_def /=.
      iIntros "Harray".
      iDestruct "Harray" as (len Hlen Hrange) "_".
      iExists 1%N. iSplit; [done |]. iSplit; [iPureIntro; nia | done].
    - rewrite /bytes_of_u64s /=.
      iIntros "Harray".
      iDestruct (mem_mapsto_array_app 64%N a q [value] values
        with "[Harray]") as "[Hhead Htail]".
      { iEval (rewrite /=). iExact "Harray". }
      iDestruct (mem_mapsto_array_singleton with "Hhead") as "Hvalue".
      iDestruct (mem_mapsto_mapsto_to_byte_array with "Hvalue") as "Hhead".
      iDestruct ("IH" $! (a + 8)%Z with "Htail") as "Htail".
      iApply (mem_mapsto_array_app_combine 8%N a q with "Hhead").
      have Hchunk :
        length (bv_to_little_endian 8 8 (bv_unsigned value)) = 8%nat.
      { rewrite length_bv_to_little_endian; [done | lia]. }
      rewrite Hchunk /=. iExact "Htail".
  Qed.

  Lemma mem_mapsto_bytes_to_u64_array (a : Z) q
      (values : list (bv 64)) :
    a ↦ₘ{q}∗ bytes_of_u64s values -∗ a ↦ₘ{q}∗ values.
  Proof.
    iInduction values as [|value values] "IH" forall (a).
    - rewrite /bytes_of_u64s /= !mem_mapsto_array_eq
        /mem_mapsto_array_def /=.
      iIntros "Harray".
      iDestruct "Harray" as (len Hlen Hrange) "_".
      iExists 8%N. iSplit; [done |]. iSplit; [iPureIntro; nia | done].
    - rewrite /bytes_of_u64s /=.
      iIntros "Harray".
      iDestruct (mem_mapsto_array_app 8%N a q
        (bv_to_little_endian 8 8 (bv_unsigned value))
        (bytes_of_u64s values) with "Harray") as "[Hhead Htail]".
      iDestruct (mem_mapsto_byte_array_to_mapsto with "Hhead") as "Hvalue".
      have Hchunk :
        length (bv_to_little_endian 8 8 (bv_unsigned value)) = 8%nat.
      { rewrite length_bv_to_little_endian; [done | lia]. }
      iEval (rewrite Hchunk /=) in "Hvalue".
      have Hround :
        Z_to_bv 64
          (little_endian_to_bv 8
            (bv_to_little_endian 8 8 (bv_unsigned value))) = value.
      { apply Z_to_bv_little_endian_to_bv_to_little_endian; [lia | done]. }
      iEval (rewrite Hround) in "Hvalue".
      iDestruct (mem_mapsto_array_singleton with "Hvalue") as "Hhead".
      iDestruct ("IH" $! (a + 8)%Z with "[Htail]") as "Htail".
      { iEval (rewrite Hchunk /=) in "Htail".
        iExact "Htail". }
      iApply (mem_mapsto_array_app_combine 64%N a q [value] values
        with "Hhead").
      iExact "Htail".
  Qed.

  Lemma mem_mapsto_array_region n (a : Z) q
      (values : list (bv n)) (start count : nat) :
    (start + count <= length values)%nat ->
    a ↦ₘ{q}∗ values -∗
    a ↦ₘ{q}∗ take start values ∗
    (a + Z.of_N (n `div` 8) * Z.of_nat start) ↦ₘ{q}∗
      take count (drop start values) ∗
    (a + Z.of_N (n `div` 8) * Z.of_nat (start + count)) ↦ₘ{q}∗
      drop (start + count) values.
  Proof.
    iIntros (Hbounds) "Harray".
    iDestruct (mem_mapsto_array_app n a q
      (take start values) (drop start values) with "[Harray]") as
      "[Hprefix Hrest]".
    { rewrite take_drop. iExact "Harray". }
    have Hstart : length (take start values) = start.
    { rewrite length_take. lia. }
    iEval (rewrite Hstart) in "Hrest".
    iDestruct (mem_mapsto_array_app n
      (a + Z.of_N (n `div` 8) * Z.of_nat start) q
      (take count (drop start values)) (drop count (drop start values))
      with "[Hrest]") as
      "[Hregion Hsuffix]".
    { rewrite take_drop. iExact "Hrest". }
    iEval (rewrite drop_drop) in "Hsuffix".
    iFrame.
    replace
      (a + Z.of_N (n `div` 8) * start +
       Z.of_N (n `div` 8) * length (take count (drop start values)))%Z with
      (a + Z.of_N (n `div` 8) * Z.of_nat (start + count))%Z.
    - iExact "Hsuffix".
    - rewrite length_take length_drop Nat.min_l; lia.
  Qed.

End array_regions.

Section array_region_subsumption.
  Context `{!islaG Sigma}.

  Definition array_region_start (elementBits : N) (base requested : Z) : nat :=
    Z.to_nat ((requested - base) / Z.of_N (elementBits `div` 8)).

  Lemma subsume_mem_array_region A a1 a2 n
      (available : list (bv n)) (requested : A -> list (bv n)) G :
    ((∃ x,
      let start := array_region_start n a1 a2 in
      let count := length (requested x) in
      ⌜(0 < Z.of_N (n `div` 8))%Z⌝ ∗
      ⌜a2 = (a1 + Z.of_N (n `div` 8) * Z.of_nat start)%Z⌝ ∗
      ⌜requested x = take count (drop start available)⌝ ∗
      ⌜(start + count <= length available)%nat⌝ ∗
      (a1 ↦ₘ∗ take start available -∗
      (a1 + Z.of_N (n `div` 8) * Z.of_nat (start + count)) ↦ₘ∗
        drop (start + count) available -∗
      G x))%I)
    ⊢ subsume (a1 ↦ₘ∗ available) (fun x : A => a2 ↦ₘ∗ requested x) G.
  Proof.
    iIntros "Hrule Harray".
    iDestruct "Hrule" as (x) "Hrule".
    iDestruct "Hrule" as
      "(%Hwidth & %Haddress & %Hrequested & %Hbounds & Hcontinue)".
    set (start := array_region_start n a1 a2) in *.
    set (count := length (requested x)) in *.
    iDestruct (mem_mapsto_array_region n a1 (DfracOwn 1)
      available start count with "Harray") as
      "[Hprefix [Hregion Hsuffix]]"; [done |].
    iExists x. iSplitL "Hregion".
    - rewrite Haddress Hrequested. iExact "Hregion".
    - iApply ("Hcontinue" with "Hprefix Hsuffix").
  Qed.

  Definition subsume_mem_array_region_inst :=
    [instance @subsume_mem_array_region].
  Global Existing Instance subsume_mem_array_region_inst | 100.

End array_region_subsumption.

Lemma array_region_start_64_same base :
  array_region_start 64 base base = 0%nat.
Proof.
  rewrite /array_region_start Z.sub_diag. reflexivity.
Qed.

#[export] Hint Rewrite array_region_start_64_same : lithium_rewrite.

Section array_element_subsumption.
  Context `{!islaG Sigma}.

  Lemma subsume_mem_array_element A (a1 a2 : Z) n
      (available : list (bv n)) (requested : A -> bv n) G :
    ((∃ x,
      let start := array_region_start n a1 a2 in
      ⌜(0 < Z.of_N (n `div` 8))%Z⌝ ∗
      ⌜a2 = (a1 + Z.of_N (n `div` 8) * Z.of_nat start)%Z⌝ ∗
      ⌜take 1 (drop start available) = [requested x]⌝ ∗
      ⌜(start + 1 <= length available)%nat⌝ ∗
      (a1 ↦ₘ∗ take start available -∗
       (a1 + Z.of_N (n `div` 8) * Z.of_nat (start + 1)) ↦ₘ∗
         drop (start + 1) available -∗ G x))%I)
    ⊢ subsume (a1 ↦ₘ∗ available) (fun x : A => a2 ↦ₘ requested x) G.
  Proof.
    iIntros "Hrule Harray".
    iDestruct "Hrule" as (x) "Hrule".
    iDestruct "Hrule" as
      "(%Hwidth & %Haddress & %Hrequested & %Hbounds & Hcontinue)".
    set (start := array_region_start n a1 a2) in *.
    iDestruct (mem_mapsto_array_region n a1 (DfracOwn 1)
      available start 1 with "Harray") as
      "[Hprefix [Hregion Hsuffix]]"; [done |].
    iExists x. iSplitL "Hregion".
    - rewrite Haddress Hrequested mem_mapsto_array_singleton.
      iExact "Hregion".
    - iApply ("Hcontinue" with "Hprefix Hsuffix").
  Qed.

  Definition subsume_mem_array_element_inst :=
    [instance @subsume_mem_array_element].
  Global Existing Instance subsume_mem_array_element_inst | 95.

  Lemma subsume_mem_array_element_total (a1 a2 : Z) n
      (available : list (bv n)) `{!Inhabited (bv n)} G :
    ((let start := array_region_start n a1 a2 in
      ⌜(0 < Z.of_N (n `div` 8))%Z⌝ ∗
      ⌜a2 = (a1 + Z.of_N (n `div` 8) * Z.of_nat start)%Z⌝ ∗
      ⌜(start < length available)%nat⌝ ∗
      (a1 ↦ₘ∗ take start available -∗
       (a1 + Z.of_N (n `div` 8) * Z.of_nat (start + 1)) ↦ₘ∗
         drop (start + 1) available -∗
       G (available !!! start, tt)ₗ))%I)
    ⊢ subsume (a1 ↦ₘ∗ available)
        (fun x : bv n *ₗ () => a2 ↦ₘ x.1ₗ) G.
  Proof.
    iIntros "Hrule".
    set (start := array_region_start n a1 a2).
    iDestruct "Hrule" as "(%Hwidth & %Haddress & %Hbounds & Hcontinue)".
    iApply subsume_mem_array_element.
    iExists (available !!! start, tt)ₗ. cbn.
    iSplit; [done |]. iSplit; [done |].
    iSplit.
    - have Hlookup : available !! start = Some (available !!! start).
      { apply list_lookup_lookup_total_lt. exact Hbounds. }
      rewrite (drop_S available (available !!! start) start Hlookup). done.
    - iSplit; [iPureIntro; lia |]. iExact "Hcontinue".
  Qed.

  Definition subsume_mem_array_element_total_inst :=
    [instance @subsume_mem_array_element_total].
  Global Existing Instance subsume_mem_array_element_total_inst | 94.

End array_element_subsumption.

Section byte_array_word_subsumption.
  Context `{!islaG Sigma}.

  Lemma subsume_mem_byte_array_u64 A (a1 a2 : Z)
      (available : list (bv 8)) (requested : A -> bv 64)
      (G : A -> iProp Sigma) :
    ((∃ x,
      let start := Z.to_nat (a2 - a1) in
      let bytes := take 8 (drop start available) in
      ⌜a2 = (a1 + Z.of_nat start)%Z⌝ ∗
      ⌜(start + 8 <= length available)%nat⌝ ∗
      ⌜requested x = Z_to_bv 64 (little_endian_to_bv 8 bytes)⌝ ∗
      (a1 ↦ₘ∗ take start available -∗
       (a1 + Z.of_nat (start + 8))%Z ↦ₘ∗
         drop (start + 8) available -∗ G x))%I)
    ⊢ subsume (a1 ↦ₘ∗ available) (fun x : A => a2 ↦ₘ requested x) G.
  Proof.
    iIntros "Hrule Harray".
    iDestruct "Hrule" as (x) "(%Haddress & %Hbounds & %Hvalue & Hcontinue)".
    set (start := Z.to_nat (a2 - a1)) in *.
    set (bytes := take 8 (drop start available)) in *.
    iDestruct (mem_mapsto_array_region 8%N a1 (DfracOwn 1)
      available start 8 with "Harray") as
      "[Hprefix [Hregion Hsuffix]]"; [done |].
    iDestruct (mem_mapsto_byte_array_to_mapsto with "Hregion") as "Hregion".
    have Hbytes : length bytes = 8%nat.
    { rewrite /bytes length_take length_drop Nat.min_l; lia. }
    iExists x. iSplitL "Hregion".
    - rewrite Haddress Hvalue.
      iEval (rewrite Hbytes /= Z.mul_1_l) in "Hregion". iExact "Hregion".
    - iEval (cbn; rewrite Z.mul_1_l) in "Hsuffix".
      iApply ("Hcontinue" with "Hprefix Hsuffix").
  Qed.

  Definition subsume_mem_byte_array_u64_inst :=
    [instance @subsume_mem_byte_array_u64].
  Global Existing Instance subsume_mem_byte_array_u64_inst | 95.

End byte_array_word_subsumption.

Section uninitialized_region_subsumption.
  Context `{!islaG Sigma}.

  Lemma subsume_mem_uninit_region A a1 a2 n1 n2 G :
    ((⌜(0 <= n2 /\ a1 <= a2 /\ a2 + n2 <= a1 + n1)%Z⌝ ∗
      (
      a1 ↦ₘ? (a2 - a1) -∗
      (a2 + n2) ↦ₘ? (a1 + n1 - (a2 + n2)) -∗
      ∃ x : A, G x))%I)
    ⊢ subsume (a1 ↦ₘ? n1) (fun _ : A => a2 ↦ₘ? n2) G.
  Proof.
    iIntros "(%Hbounds & Hcontinue) Hmemory".
    iDestruct (mem_mapsto_uninit_split (a2 - a1) with "Hmemory") as
      "[Hprefix Hrest]"; [lia |].
    have Hbase : (a1 + (a2 - a1) = a2)%Z by lia.
    iEval (rewrite Hbase) in "Hrest".
    iDestruct (mem_mapsto_uninit_split n2 with "Hrest") as
      "[Hregion Hsuffix]"; [lia |].
    iDestruct ("Hcontinue" with "Hprefix [Hsuffix]") as (x) "Hcontinue".
    { replace (n1 - (a2 - a1) - n2)%Z with
        (a1 + n1 - (a2 + n2))%Z by lia.
      iExact "Hsuffix". }
    iExists x. iFrame.
  Qed.

  Definition subsume_mem_uninit_region_inst :=
    [instance @subsume_mem_uninit_region].
  Global Existing Instance subsume_mem_uninit_region_inst | 100.

End uninitialized_region_subsumption.

Section uninitialized_array_subsumption.
  Context `{!islaG Sigma}.

  Lemma subsume_mem_uninit_byte_array A a1 a2 n1
      (requested : A -> list (bv 8)) G :
    ((∃ x,
      let n2 := Z.of_nat (length (requested x)) in
      ⌜(0 <= n2 ∧ a1 <= a2 ∧ a2 + n2 <= a1 + n1)%Z⌝ ∗
      (a1 ↦ₘ? (a2 - a1) -∗
      (a2 + n2) ↦ₘ? (a1 + n1 - (a2 + n2)) -∗
      ∀ values : list (bv 8),
        ⌜Z.of_nat (length values) = n2⌝ -∗
        ⌜requested x = values⌝ ∗ G x))%I)
    ⊢ subsume (a1 ↦ₘ? n1) (fun x : A => a2 ↦ₘ∗ requested x) G.
  Proof.
    iIntros "Hrule Hmemory".
    iDestruct "Hrule" as (x) "(%Hbounds & Hcontinue)".
    set (n2 := Z.of_nat (length (requested x))) in *.
    iDestruct (mem_mapsto_uninit_split (a2 - a1) with "Hmemory") as
      "[Hprefix Hrest]"; [lia |].
    have Hbase : (a1 + (a2 - a1) = a2)%Z by lia.
    iEval (rewrite Hbase) in "Hrest".
    iDestruct (mem_mapsto_uninit_split n2 with "Hrest") as
      "[Hregion Hsuffix]"; [lia |].
    iDestruct (mem_mapsto_uninit_to_byte_array with "Hregion") as
      (values Hlength) "Hregion".
    iDestruct ("Hcontinue" with "Hprefix [Hsuffix]") as "Hcontinue".
    { replace (n1 - (a2 - a1) - n2)%Z with
        (a1 + n1 - (a2 + n2))%Z by lia.
      iExact "Hsuffix". }
    iSpecialize ("Hcontinue" $! values).
    iDestruct ("Hcontinue" with "[]") as "(%Hrequested & Hcontinue)".
    { iPureIntro. exact Hlength. }
    iExists x. rewrite Hrequested. iFrame.
  Qed.

  Definition subsume_mem_uninit_byte_array_inst :=
    [instance @subsume_mem_uninit_byte_array].
  Global Existing Instance subsume_mem_uninit_byte_array_inst | 90.

End uninitialized_array_subsumption.
