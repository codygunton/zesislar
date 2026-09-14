Require Import isla.riscv64.riscv64.
Require Import ZesuMachineMap.Machine.
Require Export ZesuSsz.Automation.ByteArrays.
Require Export ZesuSsz.Automation.Hooks.
Require Export ZesuSsz.Automation.ArrayCursors.
Require Import ZesuSsz.Automation.ArrayByteValues.
Require Import ZesuSsz.Automation.ArraySlices.
Require Import ZesuSsz.Contracts.IslarisMemory.
Require Import ZesuSsz.Automation.PackedWordValues.
Require Export ZesuSsz.Automation.ResourceGroups.
Require Import ZesuSsz.Automation.NatBounds.
From iris.proofmode Require Import environments.

Ltac zesu_saturate_alignment :=
  match goal with
  | H : bv_extract 0 _ _ = _ |- _ => bv_saturate
  | H : Z.land (bv_unsigned _) _ = _ |- _ => bv_saturate
  end.

Ltac zesu_finish_little_endian :=
  match goal with
  | |- context[Z_to_little_endian _ _ _] =>
      rewrite /Z_to_little_endian /=;
      rewrite !Z.land_ones; [|lia..];
      rewrite !Z.shiftr_div_pow2; [|lia..];
      repeat eexists; repeat split; reflexivity
  end.

Ltac zesu_finish_tag_bound :=
  solve [eapply zesu_aligned_tag_end;
    [eassumption | first [reflexivity | eassumption] | eassumption]].

Ltac zesu_finish_mask :=
  lazymatch goal with
  | |- bv_and _ _ = _ =>
      solve [apply bv_eq; rewrite bv_and_unsigned; simpl; assumption]
  end.

Ltac zesu_finish_constant :=
  lazymatch goal with
  | |- @eq (bv _) _ _ =>
      timeout 1 (solve [apply bv_eq; vm_compute; reflexivity])
  end.

Ltac zesu_normalize_memory_constants :=
  repeat match goal with
  | |- context[mem_mapsto _ _ (bv_add ?left ?right)] =>
      let value := constr:(bv_add left right) in
      let integer := eval vm_compute in (bv_unsigned value) in
      lazymatch integer with Z0 => idtac | Zpos _ => idtac | Zneg _ => idtac end;
      let Hconstant := fresh "Hconstant" in
      assert (Hconstant : value = BV 64 integer) by
        (apply bv_eq; vm_compute; reflexivity);
      rewrite Hconstant; clear Hconstant
  end.

Ltac zesu_normalize_memory_addresses :=
  repeat match goal with
  | Hlower : (?minimum <= bv_unsigned ?pointer)%Z,
    Hupper : (bv_unsigned ?pointer2 + _ < ?maximum)%Z
    |- context[mem_mapsto (bv_unsigned (bv_add ?base ?offset)) _ _] =>
      constr_eq base pointer;
      constr_eq pointer pointer2;
      let low := eval vm_compute in minimum in
      let high := eval vm_compute in maximum in
      let ramLow := eval vm_compute in ((mapRamBase defaultMap)%Z) in
      let ramHigh := eval vm_compute in ((machineRamEnd defaultMap)%Z) in
      constr_eq low ramLow; constr_eq high ramHigh;
      let integer := eval vm_compute in (bv_unsigned offset) in
      lazymatch integer with Z0 => idtac | Zpos _ => idtac | Zneg _ => idtac end;
      let Haddress := fresh "Haddress" in
      assert (Haddress : bv_unsigned (bv_add pointer offset) =
        (bv_unsigned pointer + integer)%Z) by
        (clear -Hlower Hupper; bv_solve);
      rewrite Haddress; clear Haddress
  end.

Ltac zesu_finish_ram_address :=
  match goal with
  | Hlower : ((mapRamBase defaultMap) <= bv_unsigned ?pointer)%Z,
    Hupper : (bv_unsigned ?pointer + _ < (machineRamEnd defaultMap))%Z |- _ =>
      lazymatch goal with
      | |- context[pointer] => solve [clear -Hlower Hupper; bv_solve]
      end
  end.

Ltac zesu_finish_pointer_alignment :=
  lazymatch goal with
  | |- bv_extract _ _ _ = _ => idtac
  end;
  match goal with
  | Halign : bv_unsigned ?pointer `mod` _ = 0 |- _ =>
      lazymatch goal with
      | |- context[pointer] => solve [clear -Halign; bv_solve]
      end
  | Halign : bv_extract 0 _ ?pointer = _ |- _ =>
      lazymatch goal with
      | |- context[pointer] =>
          solve [clear -Halign; bv_simplify_arith Halign; bv_solve]
      end
  end.

Ltac zesu_finish_ram_known :=
  lazymatch goal with
  | |- bv_unsigned ?pointer >= _ =>
      solve [change (bv_unsigned pointer >= (mapRamBase defaultMap))%Z;
        apply Z.le_ge; assumption]
  | |- bv_unsigned ?pointer < _ =>
      solve [change (bv_unsigned pointer < (machineRamEnd defaultMap))%Z; assumption]
  end.

Ltac zesu_finish_array_byte_lookup :=
  zesu_normalize_array_byte_lookups;
  repeat match goal with
  | Hlookup : ?bytes !! Z.to_nat (bv_unsigned ?offset `div` 1) = Some ?byte |- _ =>
      let integer := eval vm_compute in (bv_unsigned offset) in
      lazymatch integer with Z0 => idtac | Zpos _ => idtac end;
      let index := eval vm_compute in (Z.to_nat integer) in
      change (bytes !! index = Some byte) in Hlookup
  end;
  repeat match goal with
  | Hlookup : ?bytes !! ?index = Some ?byte
    |- context[default _ (?bytes !! ?index)] => rewrite Hlookup
  end;
  reflexivity.

Ltac zesu_normalize_equal_array_regions :=
  repeat match goal with
  | |- context[array_region_start 8 ?a ?b] =>
    let Hsame := fresh "HregionSame" in
    assert (Hsame : a = b) by bv_solve;
    rewrite (array_region_start_equal a b Hsame); clear Hsame
  end.
Ltac zesu_normalize_known_list_lengths :=
  repeat progress (rewrite ?length_take ?length_drop ?length_app);
  repeat match goal with
  | Hlen : length ?xs = ?n |- context[length ?xs] => rewrite Hlen
  end;
  cbn [Nat.min Nat.sub].
Ltac zesu_finish_known_list_shape :=
  lazymatch goal with
  | |- envs_entails _ _ => fail 0
  | |- context[array_region_start 8 _ _] => idtac
  | |- context[length _] => idtac
  | |- @eq (list _) _ _ => idtac
  | _ => fail 0
  end;
  zesu_normalize_equal_array_regions;
  cbn [drop];
  first [solve [zesu_normalize_known_list_lengths; reflexivity] |
    solve [repeat match goal with
      | |- context[take ?n ?xs] =>
        let Htake := fresh "Htake" in
        assert (Htake : (length xs <= n)%nat) by
          (zesu_normalize_known_list_lengths; lia);
        rewrite (take_ge xs n Htake); clear Htake
      end; reflexivity] |
    solve [zesu_normalize_known_list_lengths; lia] |
    solve [bv_solve]].

Ltac zesu_finish :=
  try autorewrite with zesu_indices;
  try (timeout 2 zesu_normalize_memory_constants);
  try (timeout 2 zesu_normalize_memory_addresses);
  try iAssumption;
  lazymatch goal with
  | |- SHELVED_SIDECOND _ =>
      first [solve [unshelve_sidecond; unLET; timeout 15 zesu_array_eight_value] |
        prepare_sidecond]
  | _ => unLET
  end;
  try autorewrite with zesu_indices;
  try iAssumption;
  try (timeout 2 zesu_normalize_array_cursors);
  try (timeout 2 zesu_finish_known_list_shape);
  try (timeout 2 zesu_finish_pure_resources);
  try reflexivity;
  try zesu_finish_packed_word_equality;
  try (timeout 2 (lazymatch goal with
    | |- @eq (bv 64) _ (Z_to_bv 64
        (little_endian_to_bv 8 (take 8 (drop _ _)))) =>
        solve [zesu_array_eight_value]
    end));
  try simpl;
  try done;
  try assumption;
  zesu_normalize_nat_powers;
  try zesu_finish_tag_bound;
  try zesu_finish_mask;
  try zesu_finish_array_byte_lookup;
  try zesu_finish_constant;
  try (apply Z.le_ge; assumption);
  try zesu_finish_ram_known;
  try zesu_finish_ram_address;
  try zesu_finish_pointer_alignment;
  try zesu_saturate_alignment;
  try lia;
  try bv_solve;
  try zesu_finish_little_endian.

Ltac zesu_finish_framed_wand :=
  lazymatch goal with
  | |- envs_entails _ ((?available -∗ ?requested) ∗ True)%I =>
      let Hpost := lazymatch goal with
        | |- envs_entails (Envs _ _ ?counter) _ => constr:(IAnon counter)
        end in
      iSplit;
      [iIntros "?"; rewrite ?Z_to_bv_bv_unsigned;
       timeout 5 (iFrame "∗");
       iEval (rewrite !bi.sep_True) in Hpost; iExact Hpost | done]
  end.

Ltac zesu_finish_closed_wand :=
  lazymatch goal with
  | |- envs_entails _ ((?available -∗ ?requested) ∗ ?rest)%I =>
      iSplitL "";
      [first [solve [iIntros "?"; iAssumption] |
        unshelve (repeat zesu_liAStep; liShow);
        lazymatch goal with
        | |- envs_entails _ _ => fail "closed wand needs external resources"
        | _ => zesu_finish
        end; done] |
       unshelve (repeat zesu_liAStep; liShow);
       first [zesu_finish_closed_wand | zesu_finish_framed_wand | zesu_finish]]
  end.

Ltac zesu_solve_instances :=
  lazymatch goal with
  | |- heapG _ => typeclasses eauto
  | |- islaG _ => typeclasses eauto
  | |- threadG => typeclasses eauto
  end.

Ltac zesu_pack_shaped_register_value register :=
  iSelect (register ↦ᵣ _)%I ltac:(fun H =>
    let entry := iTypeOf H in
    lazymatch entry with
    | Some (_, _ ↦ᵣ ?value)%I =>
        iExists (value, tt)ₗ; iFrame H;
        first [done | solve [iPureIntro; first [assumption | done]] |
          iSplit; [solve [iPureIntro; first [assumption | done]] |]]
    end).

Ltac zesu_pack_shaped_register_goal :=
  first
    [ lazymatch goal with
      | |- envs_entails _
          (∃ x : li_prod valu unit,
            ⌜valu_has_shape (li_fst x) (BitsShape 64)⌝ ∗
            ?register ↦ᵣ (li_fst x) ∗ _)%I =>
          zesu_pack_shaped_register_value register
      end
    | lazymatch goal with
      | |- envs_entails _
          (∃ x : li_prod valu unit,
            ⌜valu_has_shape (li_fst x) (BitsShape 64)⌝ ∗
            ?register ↦ᵣ (li_fst x))%I =>
          zesu_pack_shaped_register_value register
      end ].

Ltac zesu_pack_owned_word_goal :=
  lazymatch goal with
  | |- envs_entails _ (@bi_exist _ (li_prod (bv ?width) unit) ?body) =>
    lazymatch body with
    | context[(?address ↦ₘ{?q} (li_fst _))%I] =>
      iSelect (address ↦ₘ{q} _)%I ltac:(fun H =>
        let entry := iTypeOf H in
        lazymatch entry with
        | Some (_, (_ ↦ₘ{_} ?value)%I) =>
            iExists (value, tt)ₗ; iFrame H; try done
        end)
    end
  end.

Ltac zesu_pack_owned_register_goal :=
  lazymatch goal with
  | |- envs_entails _ (@bi_exist _ (li_prod valu unit) ?body) =>
    lazymatch body with
    | context[(@reg_mapsto _ _ _ ?register ?fraction (li_fst _))] =>
        zesu_pack_shaped_register_value register
    end
  end.

Ltac zesu_run_pass :=
  try zesu_prepare_uninit_goal;
  try zesu_normalize_find_mem_address;
  unshelve (time "zesu_run" repeat first [zesu_finish_pure_resources | zesu_pack_owned_register_goal | zesu_pack_shaped_register_goal | zesu_pack_owned_word_goal | zesu_normalize_packed_word_subsume | zesu_liAStep]; liShow;
    try zesu_finish_closed_wand;
    try zesu_finish_framed_wand;
    zesu_finish).

Ltac zesu_run :=
  unshelve (repeat progress
    (zesu_run_pass; try zesu_solve_instances; zesu_finish));
  try zesu_solve_instances.

Ltac zesu_block :=
  iStartProof;
  simpl;
  repeat first [progress iIntros (?) | progress iIntros "#?" |
    progress iIntros "?"];
  repeat iDestruct select (_ ∗ _)%I as "[? ?]";
  zesu_run.

Ltac zesu_run_until boundary :=
  first [boundary tt |
    first [liUnfoldLate | zesu_liAStep]; zesu_run_until boundary | idtac].

Ltac zesu_known_array_values :=
  repeat match goal with
  | Hread : ?bytes !! ?index = Some ?value,
    Hknown : ?bytes !! ?known_index = Some ?known_value |- _ =>
      is_var value;
      tryif constr_eq value known_value then fail 1 else idtac;
      let Hindex := fresh "Hindex" in
      assert (Hindex : index = known_index) by
        (unLET; autorewrite with zesu_indices;
         rewrite ?Z.div_1_r; reflexivity);
      rewrite Hindex Hknown in Hread;
      injection Hread as Hread; subst value
  end.

Ltac zesu_finish_array_branch :=
  unLET; zesu_known_array_values; exfalso;
  first [bv_solve | match goal with
    | Hbranch : _ <> _ |- _ => bv_simplify Hbranch; congruence
    end | match goal with
    | Htag : ?tag <> _, Hbranch : bv_zero_extend _ ?tag = _ |- _ =>
        bv_simplify Htag; bv_simplify Hbranch; lia
    end].

Ltac zesu_tuple_witness T :=
  lazymatch T with
  | li_prod ?A ?B =>
      let head := open_constr:(_ : A) in
      let tail := zesu_tuple_witness B in constr:(li_pair head tail)
  | unit => constr:(tt)
  end.

Ltac zesu_instantiate_tuple :=
  lazymatch goal with
  | |- envs_entails _ (@bi_exist _ ?T _) =>
      let witness := zesu_tuple_witness T in iExists witness
  end.

Ltac zesu_handoff := zesu_instantiate_tuple; zesu_run.

Ltac zesu_frame_handoff := timeout 5 (iFrame "∗"; zesu_run).

Tactic Notation "zesu_pack" constr(witness) :=
  iExists witness;
  iFrame;
  try done;
  try zesu_finish.
