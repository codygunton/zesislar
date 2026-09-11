From Coq Require Import Lists.List ZArith.ZArith.
From iris.proofmode Require Import environments.
From iris.program_logic Require Import lifting.
Require Import isla.riscv64.riscv64.
Require Import InstrSpecs.Specs.
Require Import ZesuSsz.Contracts.IslarisMemory.

Import ListNotations.

Definition zesu_byte_access_size (len : N) : bool :=
  (len =? 1)%N || (len =? 2)%N || (len =? 4)%N || (len =? 8)%N.

Lemma zesu_bv_sign_extend_same (n : N) (value : bv n) :
  bv_sign_extend n value = value.
Proof. apply bv_sign_extend_idemp. Qed.

Lemma zesu_bv_unsigned_add_Z_64 (base : bv 64) (offset : Z) :
  (0 <= offset)%Z ->
  (bv_unsigned base + offset < 2 ^ 64)%Z ->
  bv_unsigned (base + Z_to_bv 64 offset)%bv - bv_unsigned base = offset.
Proof. intros. bv_solve. Qed.

Lemma zesu_bv_unsigned_add_no_wrap_64 (base offset : bv 64) :
  (bv_unsigned base + bv_unsigned offset < 2 ^ 64)%Z ->
  bv_unsigned (base + offset)%bv - bv_unsigned base = bv_unsigned offset.
Proof. intros. bv_solve. Qed.

#[export] Hint Rewrite zesu_bv_sign_extend_same : zesu_indices.
#[export] Hint Rewrite zesu_bv_unsigned_add_Z_64 using bv_solve
  : zesu_indices.
#[export] Hint Rewrite zesu_bv_unsigned_add_no_wrap_64 using bv_solve
  : zesu_indices.

Lemma zesu_take_8_drop (bytes : list (bv 8)) (offset : nat) :
  (offset + 8 <= length bytes)%nat ->
  take 8 (drop offset bytes) =
    [default (BV 8 0) (bytes !! offset);
     default (BV 8 0) (bytes !! (offset + 1)%nat);
     default (BV 8 0) (bytes !! (offset + 2)%nat);
     default (BV 8 0) (bytes !! (offset + 3)%nat);
     default (BV 8 0) (bytes !! (offset + 4)%nat);
     default (BV 8 0) (bytes !! (offset + 5)%nat);
     default (BV 8 0) (bytes !! (offset + 6)%nat);
     default (BV 8 0) (bytes !! (offset + 7)%nat)].
Proof.
  intros Hlength.
  have Hbyte (index : nat) (Hindex : (index < length bytes)%nat) :
      bytes !! index = Some (default (BV 8 0) (bytes !! index)).
  { destruct (nth_lookup_or_length bytes index (BV 8 0)) as [Hlookup|Hlookup].
    - rewrite Hlookup. reflexivity.
    - lia. }
  apply list_eq. intros index.
  destruct index as [|index].
  { rewrite lookup_take; [|lia]. rewrite lookup_drop /=.
    replace (offset + 0)%nat with offset by lia.
    rewrite (Hbyte offset ltac:(lia)). reflexivity. }
  destruct index as [|index].
  { rewrite lookup_take; [|lia]. rewrite lookup_drop /=.
    rewrite (Hbyte (offset + 1)%nat ltac:(lia)). reflexivity. }
  destruct index as [|index].
  { rewrite lookup_take; [|lia]. rewrite lookup_drop /=.
    rewrite (Hbyte (offset + 2)%nat ltac:(lia)). reflexivity. }
  destruct index as [|index].
  { rewrite lookup_take; [|lia]. rewrite lookup_drop /=.
    rewrite (Hbyte (offset + 3)%nat ltac:(lia)). reflexivity. }
  destruct index as [|index].
  { rewrite lookup_take; [|lia]. rewrite lookup_drop /=.
    rewrite (Hbyte (offset + 4)%nat ltac:(lia)). reflexivity. }
  destruct index as [|index].
  { rewrite lookup_take; [|lia]. rewrite lookup_drop /=.
    rewrite (Hbyte (offset + 5)%nat ltac:(lia)). reflexivity. }
  destruct index as [|index].
  { rewrite lookup_take; [|lia]. rewrite lookup_drop /=.
    rewrite (Hbyte (offset + 6)%nat ltac:(lia)). reflexivity. }
  destruct index as [|index].
  { rewrite lookup_take; [|lia]. rewrite lookup_drop /=.
    rewrite (Hbyte (offset + 7)%nat ltac:(lia)). reflexivity. }
  rewrite lookup_take_ge; [done|lia].
Qed.

Lemma zesu_assemble_8_bytes
    (b0 b1 b2 b3 b4 b5 b6 b7 : bv 8) :
  bv_or
    (bv_shiftl
      (bv_or
        (bv_or
          (bv_shiftl (bv_zero_extend 64 b7) (BV 64 24))
          (bv_shiftl (bv_zero_extend 64 b6) (BV 64 16)))
        (bv_or
          (bv_shiftl (bv_zero_extend 64 b5) (BV 64 8))
          (bv_zero_extend 64 b4)))
      (BV 64 32))
    (bv_or
      (bv_or
        (bv_shiftl (bv_zero_extend 64 b3) (BV 64 24))
        (bv_shiftl (bv_zero_extend 64 b2) (BV 64 16)))
      (bv_or
        (bv_shiftl (bv_zero_extend 64 b1) (BV 64 8))
        (bv_zero_extend 64 b0))) =
  Z_to_bv 64 (little_endian_to_bv 8 [b0; b1; b2; b3; b4; b5; b6; b7]).
Proof.
  unfold little_endian_to_bv, little_endian_to_Z.
  rewrite !fmap_cons. cbn.
  apply bv_eq. bv_simplify. bitblast as index.
  all: (f_equal; lia).
Qed.

Lemma zesu_assemble_8_bytes_at (bytes : list (bv 8)) (offset : nat) :
  (offset + 8 <= length bytes)%nat ->
  bv_or
    (bv_shiftl
      (bv_or
        (bv_or
          (bv_shiftl (bv_zero_extend 64
            (default (BV 8 0) (bytes !! (offset + 7)%nat))) (BV 64 24))
          (bv_shiftl (bv_zero_extend 64
            (default (BV 8 0) (bytes !! (offset + 6)%nat))) (BV 64 16)))
        (bv_or
          (bv_shiftl (bv_zero_extend 64
            (default (BV 8 0) (bytes !! (offset + 5)%nat))) (BV 64 8))
          (bv_zero_extend 64
            (default (BV 8 0) (bytes !! (offset + 4)%nat)))))
      (BV 64 32))
    (bv_or
      (bv_or
        (bv_shiftl (bv_zero_extend 64
          (default (BV 8 0) (bytes !! (offset + 3)%nat))) (BV 64 24))
        (bv_shiftl (bv_zero_extend 64
          (default (BV 8 0) (bytes !! (offset + 2)%nat))) (BV 64 16)))
      (bv_or
        (bv_shiftl (bv_zero_extend 64
          (default (BV 8 0) (bytes !! (offset + 1)%nat))) (BV 64 8))
        (bv_zero_extend 64 (default (BV 8 0) (bytes !! offset))))) =
  Z_to_bv 64 (little_endian_to_bv 8 (take 8 (drop offset bytes))).
Proof.
  intros Hlength. rewrite (zesu_take_8_drop bytes offset Hlength).
  apply zesu_assemble_8_bytes.
Qed.

#[export] Hint Rewrite zesu_assemble_8_bytes zesu_assemble_8_bytes_at using lia
  : zesu_byte_assembly.

Section byte_array_read.
  Context `{!islaG Sigma} `{!threadG}.

  Lemma li_wp_read_mem_zesu len n kind a vread tag ann es:
    (⌜n = (8 * len)%N⌝ ∗
    ⌜len <> 0%N⌝ ∗
    find_in_context (FindMemMapsTo (bv_unsigned a)) (fun mk =>
      match mk with
      | MKMapsTo n' vmem =>
          ∃ Heq : n = n',
            (⌜(eq_rect n bv vread n' Heq) = vmem⌝ -∗
             bv_unsigned a ↦ₘ vmem -∗ WPasm es)
      | MKArray n' a' values =>
          if (n' =? n)%N then
            ⌜(bv_unsigned a - a') `mod` Z.of_N len = 0⌝ ∗
            ∃ i : nat,
              ⌜Z.of_nat i = (bv_unsigned a - a') / Z.of_N len⌝ ∗
              ⌜(i < length values)%nat⌝ ∗
              ∃ Heq : n = n',
                (∀ vmem, ⌜values !! i = Some vmem⌝ -∗
                  ⌜(eq_rect n bv vread n' Heq) = vmem⌝ -∗
                  a' ↦ₘ∗ values -∗ WPasm es)
          else
            if zesu_byte_access_size len then
              ⌜n' = 8%N⌝ ∗
              ∃ i : nat,
                ⌜Z.of_nat i = bv_unsigned a - a'⌝ ∗
                ⌜(i + N.to_nat len <= length values)%nat⌝ ∗
                (∀ vmem,
                  ⌜vmem = Z_to_bv n
                    (little_endian_to_bv n'
                      (take (N.to_nat len) (drop i values)))⌝ -∗
                  ⌜vread = vmem⌝ -∗ a' ↦ₘ∗ values -∗ WPasm es)
            else False
      | MKUninit _ _ => False
      | MKMMIO a' length =>
          ⌜a' <= bv_unsigned a⌝ ∗
          ⌜bv_unsigned a + Z.of_N len <= a' + length⌝ ∗
          ∃ Pks Pks', spec_trace Pks ∗
            ⌜scons (SReadMem a vread) Pks' ⊆ Pks⌝ ∗
            (spec_trace Pks' -∗ WPasm es)
      end))
    ⊢ WPasm (ReadMem (RVal_Bits (@bv_to_bvn n vread)) kind
              (RVal_Bits (@bv_to_bvn 64 a)) len tag ann :t: es).
  Proof.
    iDestruct 1 as (?? mk) "[Hmem Hcont]" => /=. case_match.
    - iDestruct "Hcont" as (?) "Hcont". subst => /=.
      iApply (wp_read_mem with "Hmem Hcont"); [done|lia].
    - rename a0 into a'. destruct (n0 =? n)%N eqn:Hn.
      + apply N.eqb_eq in Hn.
        iDestruct "Hcont" as (? i Heqi [??]%lookup_lt_is_Some_2 ?) "Hcont".
        clear Hn. subst => /=.
        have {} Heqi: a' = bv_unsigned a - i * Z.of_N len.
        { rewrite Heqi Z.mul_comm -Z_div_exact_full_2; [lia|lia|done]. }
        iApply (wp_read_mem_array with "Hmem [Hcont]");
          [done|lia|done|done|].
        iIntros (?) "Hvalue". by iApply "Hcont".
      + destruct (zesu_byte_access_size len) eqn:Hsize; [|done].
        iDestruct "Hcont" as (-> i Hi Hbounds) "Hcont".
        subst n.
        iDestruct (mem_mapsto_array_region 8%N a' (DfracOwn 1)
          l i (N.to_nat len) with "Hmem") as
          "[Hprefix [Hregion Hsuffix]]"; [done|].
        have Hbytes :
          length (take (N.to_nat len) (drop i l)) = N.to_nat len.
        { rewrite length_take length_drop. lia. }
        iDestruct (mem_mapsto_byte_array_to_mapsto_len
          (N.to_nat len) with "Hregion") as "Hregion"; [done|].
        iEval (rewrite N2Nat.id) in "Hregion".
        have Haddress : (a' + Z.of_nat i)%Z = bv_unsigned a by lia.
        iEval (rewrite /= Z.mul_1_l Haddress) in "Hregion".
        iApply (wp_read_mem with "Hregion [Hcont Hprefix Hsuffix]");
          [done|lia|].
        iIntros (->) "Hword".
        iApply ("Hcont" with "[//] [//]").
        iApply (mem_mapsto_array_recombine_read (N.to_nat len) a'
          l i with "Hprefix Hsuffix [Hword]").
        * rewrite N2Nat.id.
          iEval (rewrite -Haddress) in "Hword". iExact "Hword".
        * iPureIntro.
          change (a' + 1 * Z.of_nat (i + N.to_nat len) =
            a' + Z.of_nat (i + N.to_nat len))%Z. lia.
        * iPureIntro. reflexivity.
        * iPureIntro. exact Hbounds.
    - done.
    - iDestruct "Hcont" as (?? Pks Pks') "[Hks [%Hscons Hcont]]";
        simplify_eq/=.
      iApply (wp_read_mmio with "[] [] [Hmem] Hks").
      + done.
      + lia.
      + intros snapshot _ _. specialize (Hscons [SReadMem a vread snapshot]).
        apply Hscons. right. eexists _, []. split; [done|by left].
      + rewrite /snapshot_reg_resources. done.
      + rewrite /snapshot_mem_resources. done.
      + iApply (mmio_range_shorten with "Hmem"); lia.
      + iIntros (snapshot) "_ _ Hspec". iApply "Hcont".
        iApply (spec_trace_mono with "Hspec"). spec_solver.
  Qed.
End byte_array_read.

Section byte_array_write.
  Context `{!islaG Sigma} `{!threadG}.

  (** Snapshot claims describe ordinary memory.  An MMIO write does not
      change that memory, so the continuation keeps the claims. *)
  Lemma wp_write_mmio_preserve_mem_claims n len a (vnew : bv n) es ann res
      kind tag (Pks : spec) (regClaims : list (sail_name * valu))
      (memClaims : list (Z * list byte)) :
    n = (8 * len)%N ->
    0 < Z.of_N len ->
    (forall snapshot, snapshot_reg_agreement snapshot regClaims ->
      snapshot_mem_agreement snapshot memClaims ->
      Pks [SWriteMem a vnew snapshot]) ->
    snapshot_reg_resources regClaims -∗
    snapshot_mem_resources memClaims -∗
    mmio_range (bv_unsigned a) (Z.of_N len) -∗
    spec_trace Pks -∗
    (∀ snapshot,
      ⌜snapshot_reg_agreement snapshot regClaims⌝ -∗
      ⌜snapshot_mem_agreement snapshot memClaims⌝ -∗
      snapshot_mem_resources memClaims -∗
      spec_trace (fun labels => Pks (SWriteMem a vnew snapshot :: labels)) -∗
      WPasm es) -∗
    WPasm (WriteMem (RVal_Bool res) kind
      (RVal_Bits (@bv_to_bvn 64 a)) (RVal_Bits (@bv_to_bvn n vnew))
      len tag ann :t: es).
  Proof.
    iIntros (Hwidth Hlen Haccept)
      "HregClaims HmemClaims Hmmio Hspec Hcont".
    subst. setoid_rewrite wp_asm_unfold.
    iIntros ([????]) "/= -> -> -> Hregs".
    iApply wp_lift_step; [done|].
    iIntros (sigma1 ????) "(Hctx & Hictx & Hmem)".
    iApply fupd_mask_intro; first set_solver. iIntros "Hmask".
    iDestruct (mmio_range_lookup with "Hmem Hmmio") as %Hread; [done|].
    rewrite N2Z.id in Hread.
    iDestruct (mmio_range_in_range with "Hmmio") as %Hrange.
    iDestruct (mmio_range_Forall with "Hmem Hmmio") as %HmmioBytes.
    iDestruct (snapshot_reg_resources_agree with
      "Hregs HregClaims") as %HregAgree.
    iPoseProof (snapshot_mem_resources_agree with
      "Hmem HmemClaims") as "%HmemAgree".
    iSplit.
    { iPureIntro. eexists _, _, _, _. simpl.
      econstructor; [done | by econstructor |]. simpl.
      eexists ∅, _, _. simplify_option_eq. naive_solver. }
    iIntros "!>" (????) "_". iMod "Hmask" as "_".
    inv_seq_step.
    revert select (exists _, _) => -[?[?[?[?[??]]]]].
    simplify_option_eq. destruct_and!. simplify_eq.
    iMod (spec_ctx_cons with "Hctx Hspec") as "[Hctx Hspec]";
      [apply Haccept; assumption|].
    iFrame. iModIntro. iSplitL; [|done].
    iApply ("Hcont" with "[] [] HmemClaims Hspec"); done.
  Qed.

  Lemma li_wp_write_mmio_snapshot_zesu len n success kind a (vnew : bv n)
      tag ann es claimSearchAddress :
    (⌜n = (8 * len)%N⌝ ∗
    ⌜len <> 0%N⌝ ∗
    find_in_context (FindMemMapsTo (bv_unsigned a)) (fun mmioKind =>
      match mmioKind with
      | MKMMIO mmioAddress mmioLength =>
          ⌜mmioAddress <= bv_unsigned a⌝ ∗
          ⌜bv_unsigned a + Z.of_N len <= mmioAddress + mmioLength⌝ ∗
          find_in_context (FindMemMapsTo claimSearchAddress) (fun claimKind =>
            match claimKind with
            | MKArray claimWidth claimAddress claimBytes =>
                match claimWidth as width
                  return list (bv width) -> iProp Sigma with
                | 8%N => fun claimBytes8 =>
                    ∃ Pks Pks' accept,
                      spec_trace Pks ∗
                      ⌜forall snapshot,
                        snapshot_mem_agreement snapshot
                          [(claimAddress, claimBytes8)] -> accept snapshot⌝ ∗
                      ⌜scons_snap (SWriteMem a vnew) accept Pks' ⊆ Pks⌝ ∗
                      (claimAddress ↦ₘ∗ claimBytes8 -∗
                       spec_trace Pks' -∗ WPasm es)
                | _ => fun _ => False
                end claimBytes
            | _ => False
            end)
      | _ => False
      end))
    ⊢ WPasm (WriteMem (RVal_Bool success) kind
      (RVal_Bits (@bv_to_bvn 64 a))
      (RVal_Bits (@bv_to_bvn n vnew)) len tag ann :t: es).
  Proof.
    iDestruct 1 as (Hwidth Hlen mmioKind) "[Hmmio Hrest]".
    destruct mmioKind; try done.
    iDestruct "Hrest" as "(%Hlower&%Hupper&HclaimFind)".
    iDestruct "HclaimFind" as (claimKind) "[Hclaim Hrest]".
    destruct claimKind as
      [mapWidth mapValue | claimWidth claimAddress claimBytes |
       uninitAddress uninitLength | nestedAddress nestedLength]; try done.
    destruct claimWidth; try done.
    destruct p; try done.
    destruct p; try done.
    destruct p; try done.
    destruct p; try done.
    iDestruct "Hrest" as (Pks Pks' accept)
      "(Hks&%Haccept&%Hsubset&Hcont)".
    iApply (wp_write_mmio_preserve_mem_claims n len a vnew es ann success
      kind tag Pks []
      [(claimAddress, claimBytes)] with "[] [Hclaim] [Hmmio] Hks").
    - exact Hwidth.
    - lia.
    - intros snapshot _ Hmemory.
      specialize (Hsubset [SWriteMem a vnew snapshot]). apply Hsubset.
      right. eexists _, []. split; [by apply Haccept|].
      split; [done|by left].
    - rewrite /snapshot_reg_resources. done.
    - rewrite /snapshot_mem_resources /=. iFrame.
    - iApply (mmio_range_shorten with "Hmmio"); lia.
    - iIntros (snapshot) "_ %Hmemory Hclaim Hspec".
      iEval (rewrite /snapshot_mem_resources /=) in "Hclaim".
      iDestruct "Hclaim" as "[Hclaim _]".
      iApply ("Hcont" with "Hclaim").
      iApply (spec_trace_mono with "Hspec").
      intros labels Htail. specialize (Hsubset (SWriteMem a vnew snapshot :: labels)).
      apply Hsubset. right. exists snapshot, labels. split; [by apply Haccept|].
      split; [done|by right].
  Qed.

  Lemma li_wp_write_mem_zesu len n success kind a (vnew : bv n) tag ann es:
    (⌜n = (8 * len)%N⌝ ∗
    ⌜len <> 0%N⌝ ∗
    find_in_context (FindMemMapsTo (bv_unsigned a)) (fun mk =>
      match mk with
      | MKMapsTo n' _ =>
          ⌜n' = n⌝ ∗ (bv_unsigned a ↦ₘ vnew -∗ WPasm es)
      | MKArray n' a' values =>
          if (n' =? n)%N then
            ⌜(bv_unsigned a - a') `mod` Z.of_N len = 0⌝ ∗
            ∃ i : nat,
              ⌜Z.of_nat i = (bv_unsigned a - a') / Z.of_N len⌝ ∗
              ⌜(i < length values)%nat⌝ ∗
              ∃ Heq : n = n',
                (a' ↦ₘ∗ <[i := (eq_rect n bv vnew n' Heq)]>values -∗
                 WPasm es)
          else
            if zesu_byte_access_size len then
              ⌜n' = 8%N⌝ ∗
              ∃ i : nat,
                ⌜Z.of_nat i = bv_unsigned a - a'⌝ ∗
                ⌜(i + N.to_nat len <= length values)%nat⌝ ∗
                (a' ↦ₘ∗
                  (take i values ++
                   bv_to_little_endian (N.to_nat len) n'
                     (bv_unsigned vnew) ++
                   drop (i + N.to_nat len) values) -∗ WPasm es)
            else False
      | MKUninit a' length =>
          ⌜a' <= bv_unsigned a⌝ ∗
          ⌜bv_unsigned a + Z.of_N len <= a' + length⌝ ∗
          (bv_unsigned a ↦ₘ vnew -∗
           a' ↦ₘ? (bv_unsigned a - a') -∗
           (bv_unsigned a + Z.of_N len) ↦ₘ?
             (a' + length - (bv_unsigned a + Z.of_N len)) -∗
           WPasm es)
      | MKMMIO a' length =>
          ⌜a' <= bv_unsigned a⌝ ∗
          ⌜bv_unsigned a + Z.of_N len <= a' + length⌝ ∗
          ∃ Pks Pks', spec_trace Pks ∗
            ⌜scons (SWriteMem a vnew) Pks' ⊆ Pks⌝ ∗
            (spec_trace Pks' -∗ WPasm es)
      end))
    ⊢ WPasm (WriteMem (RVal_Bool success) kind
      (RVal_Bits (@bv_to_bvn 64 a))
      (RVal_Bits (@bv_to_bvn n vnew)) len tag ann :t: es).
  Proof.
    iDestruct 1 as (? ? mk) "[Hmem Hcont]" => /=. case_match.
    - iDestruct "Hcont" as (->) "Hcont".
      iApply (wp_write_mem with "Hmem Hcont"); [done | lia].
    - rename a0 into a'. destruct (n0 =? n)%N eqn:Hn.
      + apply N.eqb_eq in Hn.
        iDestruct "Hcont" as (? i Heqi ? Heq) "Hcont".
        clear Hn. subst => /=.
        have {} Heqi: a' = bv_unsigned a - i * Z.of_N len.
        { rewrite Heqi Z.mul_comm -Z_div_exact_full_2; [lia|lia|done]. }
        iApply (wp_write_mem_array with "Hmem [Hcont]");
          [done|lia|done|done|].
        iIntros "Hvalues". by iApply "Hcont".
      + destruct (zesu_byte_access_size len) eqn:Hsize; [|done].
        iDestruct "Hcont" as (-> i Hi Hbounds) "Hcont".
        subst n.
        iDestruct (mem_mapsto_array_region 8%N a' (DfracOwn 1)
          l i (N.to_nat len) with "Hmem") as
          "[Hprefix [Hregion Hsuffix]]"; [done|].
        have HregionLength :
          length (take (N.to_nat len) (drop i l)) = N.to_nat len.
        { rewrite length_take length_drop. lia. }
        iDestruct (mem_mapsto_byte_array_to_mapsto_len
          (N.to_nat len) with "Hregion") as "Hregion"; [done|].
        iEval (rewrite N2Nat.id) in "Hregion".
        have Haddress : (a' + Z.of_nat i)%Z = bv_unsigned a by lia.
        iEval (rewrite /= Z.mul_1_l Haddress) in "Hregion".
        iApply (wp_write_mem with "Hregion [Hcont Hprefix Hsuffix]");
          [done|lia|].
        iIntros "Hword".
        iDestruct (mem_mapsto_mapsto_to_byte_array_N len with "Hword")
          as "Hmiddle".
        iEval (rewrite -Haddress) in "Hmiddle".
        iPoseProof (mem_mapsto_array_app_combine_at 8%N a'
          (DfracOwn 1) (take i l)
          (bv_to_little_endian (N.to_nat len) 8 (bv_unsigned vnew)) i
          with "Hprefix") as "Hleft".
        { rewrite length_take. lia. }
        iEval (rewrite /= Z.mul_1_l) in "Hleft".
        iSpecialize ("Hleft" with "Hmiddle").
        iPoseProof (mem_mapsto_array_app_combine_at 8%N a'
          (DfracOwn 1)
          (take i l ++
            bv_to_little_endian (N.to_nat len) 8 (bv_unsigned vnew))
          (drop (i + N.to_nat len) l) (i + N.to_nat len)
          with "Hleft") as "Hupdated".
        { rewrite length_app length_take length_bv_to_little_endian;
            [lia|lia]. }
        iEval (rewrite /= Z.mul_1_l) in "Hupdated".
        iEval (rewrite -app_assoc) in "Hupdated".
        iEval (rewrite /= Z.mul_1_l) in "Hsuffix".
        iApply "Hcont". iApply "Hupdated". iExact "Hsuffix".
    - iDestruct "Hcont" as (??) "Hcont". subst n.
      iDestruct (mem_mapsto_uninit_split (bv_unsigned a - a0)
        with "Hmem") as "[Ha1 Ha2]"; [lia|].
      iDestruct (mem_mapsto_uninit_split (Z.of_N len)
        with "Ha2") as "[Ha2 Ha3]"; [lia|].
      iDestruct (mem_mapsto_uninit_to_mapsto with "Ha2") as (?? Heq) "Hl".
      rewrite N2Z.id N.mul_comm in Heq. subst.
      have -> : a0 + (bv_unsigned a - a0) = bv_unsigned a by bv_solve.
      iApply (wp_write_mem with "Hl"); [done|lia|]. iIntros "Hl".
      iApply ("Hcont" with "Hl Ha1").
      have -> : (n0 - (bv_unsigned a - a0) - Z.of_N len) =
        (a0 + n0 - (bv_unsigned a + Z.of_N len)) by lia.
      done.
    - iDestruct "Hcont" as (?? Pks Pks') "[Hks [%Hscons Hcont]]";
        simplify_eq/=.
      iApply (wp_write_mmio with "[] [] [Hmem] Hks").
      + done.
      + lia.
      + intros snapshot _ _. specialize (Hscons [SWriteMem a vnew snapshot]).
        apply Hscons. right. eexists _, []. split; [done|by left].
      + rewrite /snapshot_reg_resources. done.
      + rewrite /snapshot_mem_resources. done.
      + iApply (mmio_range_shorten with "Hmem"); lia.
      + iIntros (snapshot) "_ _ Hspec". iApply "Hcont".
        iApply (spec_trace_mono with "Hspec"). spec_solver.
  Qed.
End byte_array_write.
