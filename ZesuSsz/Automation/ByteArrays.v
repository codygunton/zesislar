From Coq Require Import Lists.List ZArith.ZArith.
From iris.proofmode Require Import environments.
Require Import isla.riscv64.riscv64.
Require Import InstrSpecs.Specs.
Require Import ZesuSsz.Contracts.IslarisMemory.

Import ListNotations.

Definition zesu_byte_access_size (len : N) : bool :=
  (len =? 1)%N || (len =? 2)%N || (len =? 4)%N || (len =? 8)%N.

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
    - iDestruct "Hcont" as (?? Pks Pks') "[Hks [% Hcont]]";
        simplify_eq/=.
      iApply (wp_read_mmio with "[Hmem] Hks");
        [done | lia| spec_solver | | ].
      { iApply (mmio_range_shorten with "Hmem"); lia. }
      iIntros "Hspec". iApply "Hcont".
      iApply (spec_trace_mono with "Hspec"). spec_solver.
  Qed.
End byte_array_read.

Section byte_array_write.
  Context `{!islaG Sigma} `{!threadG}.

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
    - iDestruct "Hcont" as (?? Pks Pks') "[Hks [% Hcont]]";
        simplify_eq/=.
      iApply (wp_write_mmio with "[Hmem] Hks");
        [done | lia| spec_solver | | ].
      { iApply (mmio_range_shorten with "Hmem"); lia. }
      iIntros "Hspec". iApply "Hcont".
      iApply (spec_trace_mono with "Hspec"). spec_solver.
  Qed.
End byte_array_write.
