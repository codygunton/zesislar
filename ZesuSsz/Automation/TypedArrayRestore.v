Require Import ZesuSsz.Automation.CallSet.
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Contracts.IslarisMemory.
From iris.proofmode Require Import environments.

Section typed_array.
Context `{!islaG Sigma}.

Lemma zesu_mem_array_recombine_typed n (base : Z)
    (values : list (bv n)) (index : nat) (value : bv n) :
  values !! index = Some value ->
  base ↦ₘ∗ take index values -∗
  (base + Z.of_N (n `div` 8) * Z.of_nat (S index)) ↦ₘ∗ drop (S index) values -∗
  (base + Z.of_N (n `div` 8) * Z.of_nat index) ↦ₘ value -∗
  base ↦ₘ∗ values.
Proof.
  iIntros (Hlookup) "Hprefix Hsuffix Hword".
  iEval (rewrite -mem_mapsto_array_singleton) in "Hword".
  iPoseProof (mem_mapsto_array_app_combine_at n base (DfracOwn 1)
    (take index values) [value] index with "Hprefix Hword") as "Hleft".
  { rewrite length_take. apply Nat.min_l.
    apply lookup_lt_Some in Hlookup. lia. }
  iEval (rewrite -(take_S_r values index value Hlookup)) in "Hleft".
  iPoseProof (mem_mapsto_array_app_combine_at n base (DfracOwn 1)
    (take (S index) values) (drop (S index) values) (S index)
    with "Hleft Hsuffix") as "Hwhole".
  { rewrite length_take. apply Nat.min_l.
    apply lookup_lt_Some in Hlookup. lia. }
  iEval (rewrite take_drop) in "Hwhole".
  iExact "Hwhole".
Qed.

Lemma zesu_subsume_mem_array_restore_typed A (base : Z) n
    (values : list (bv n)) (index : nat) G :
  (⌜(index < length values)%nat⌝ ∗
   (base + Z.of_N (n `div` 8) * Z.of_nat (S index)) ↦ₘ∗ drop (S index) values ∗
   (base + Z.of_N (n `div` 8) * Z.of_nat index) ↦ₘ (values !!! index) ∗
   (∃ x : A, G x))%I ⊢
  subsume (base ↦ₘ∗ take index values)
    (fun _ : A => base ↦ₘ∗ values) G.
Proof.
  iIntros "(%Hbound & Hsuffix & Hword & Hcontinue) Hprefix".
  iDestruct "Hcontinue" as (x) "HG".
  iExists x. iFrame "HG".
  iApply (zesu_mem_array_recombine_typed n base values index
    (values !!! index) (list_lookup_lookup_total_lt values index Hbound)
    with "Hprefix Hsuffix Hword").
Qed.
Definition zesu_subsume_mem_array_restore_typed_inst `{!ZesuCallSet} :=
  [instance zesu_subsume_mem_array_restore_typed].
Global Existing Instance zesu_subsume_mem_array_restore_typed_inst | 0.
End typed_array.

Ltac zesu_restore_typed_array_at base values solve_conditions :=
  let kind := type of values in
  lazymatch kind with list (bv ?width) =>
    iMatchHyp ltac:(fun Hprefix prefix =>
      lazymatch prefix with
      | (?prefixBase ↦ₘ∗ take ?index ?original)%I =>
        constr_eq prefixBase base;
        constr_eq original values;
        iMatchHyp ltac:(fun Hsuffix suffix =>
          lazymatch suffix with
          | (?suffixAddress ↦ₘ∗ ?suffixValues)%I =>
            let expectedSuffix := eval cbn in (drop (S index) values) in
            let actualSuffix := eval cbn in suffixValues in
            constr_eq actualSuffix expectedSuffix;
            iMatchHyp ltac:(fun Hword word =>
              lazymatch word with
              | (?wordAddress ↦ₘ ?value)%I =>
                let wordKind := type of value in
                constr_eq wordKind (bv width);
                let Hbound := fresh "HrestoreBound" in
                assert (Hbound : (index < length values)%nat) by solve_conditions;
                let HsuffixAddress := fresh "HrestoreSuffix" in
                assert (HsuffixAddress : suffixAddress =
                  (base + Z.of_N (width `div` 8) * Z.of_nat (S index))%Z)
                  by solve_conditions;
                let HwordAddress := fresh "HrestoreWord" in
                assert (HwordAddress : wordAddress =
                  (base + Z.of_N (width `div` 8) * Z.of_nat index)%Z)
                  by solve_conditions;
                let Hlookup := fresh "HrestoreLookup" in
                assert (Hlookup : values !! index = Some value) by
                  (apply (proj2 (list_lookup_alt values index value));
                   split; [exact Hbound | solve_conditions]);
                iEval (rewrite HsuffixAddress) in Hsuffix;
                iEval (rewrite HwordAddress) in Hword;
                let Hwhole := iFresh in
                iPoseProof (zesu_mem_array_recombine_typed width base values
                  index value Hlookup) as Hwhole;
                iSpecialize (Hwhole with Hprefix);
                iSpecialize (Hwhole with Hsuffix);
                iSpecialize (Hwhole with Hword);
                clear Hbound Hlookup HsuffixAddress HwordAddress;
                iFrame Hwhole
              end)
          end)
      end)
  end.

Ltac zesu_restore_typed_array_goal solve_conditions :=
  zesu_call_set_on;
  lazymatch goal with
  | |- envs_entails _ ((?base ↦ₘ∗ ?values) ∗ _)%I =>
      zesu_restore_typed_array_at base values solve_conditions
  | |- envs_entails _ (?base ↦ₘ∗ ?values)%I =>
      zesu_restore_typed_array_at base values solve_conditions
  end.

Print Assumptions zesu_mem_array_recombine_typed.
Print Assumptions zesu_subsume_mem_array_restore_typed.
