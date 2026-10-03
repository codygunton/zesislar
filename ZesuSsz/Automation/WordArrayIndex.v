Require Import ZesuSsz.Automation.CallOwnership.
Require Import ZesuSsz.Contracts.IslarisMemory.
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Automation.ArrayLoadPriority.
From iris.proofmode Require Import environments.
Open Scope Z_scope.

Lemma zesu_word_array_offset_index (base first last : Z) :
  array_region_start 64 (base + first) (base + last) =
    Z.to_nat ((last - first) `div` 8).
Proof.
  unfold array_region_start.
  replace (base + last - (base + first)) with (last - first) by lia.
  reflexivity.
Qed.

Ltac zesu_integer_offset expression :=
  lazymatch expression with
  | Z.add ?prefix ?offset =>
      let constant := eval vm_compute in offset in
      let accepted := lazymatch constant with
      | Z0 => constr:(true) | Zpos _ => constr:(true) | Zneg _ => constr:(true)
      end in
      let result := zesu_integer_offset prefix in
      lazymatch result with
      | (?base, ?previous) =>
          let total := eval vm_compute in (previous + constant)%Z in
          constr:((base, total))
      end
  | _ => constr:((expression, 0%Z))
  end.

Ltac zesu_constant_word_array_index :=
  zesu_call_ownership_on;
  let _ := constr:(_ : ZesuStepArrayLoadPriority) in
  match goal with
  | |- context[array_region_start 64 ?start ?finish] =>
      let offsetsLeft := zesu_integer_offset start in
      let offsetsRight := zesu_integer_offset finish in
      lazymatch offsetsLeft with
      | (?base, ?first) =>
          lazymatch offsetsRight with
          | (?root, ?last) =>
              constr_eq base root;
              let index := eval vm_compute in (Z.to_nat ((last - first) `div` 8)) in
              let Hindex := fresh "HconstantWordIndex" in
              assert (Hindex : array_region_start 64 start finish = index) by
                (replace start with (base + first)%Z by lia;
                 replace finish with (base + last)%Z by lia;
                 rewrite zesu_word_array_offset_index; reflexivity);
              progress rewrite Hindex; clear Hindex
          end
      end
  end.

Print Assumptions zesu_word_array_offset_index.

Ltac zesu_constant_word_array_lookup :=
  zesu_call_ownership_on;
  let _ := constr:(_ : ZesuStepArrayLoadPriority) in
  match goal with
  | Hlookup : ?values !! Z.to_nat
      ((bv_unsigned (bv_add ?sp ?offset) - ?start) `div` 8) = Some ?loaded |- _ =>
      let positions := zesu_integer_offset start in
      lazymatch positions with
      | (?base, ?first) =>
          constr_eq base (bv_unsigned sp);
          let last := eval vm_compute in (bv_unsigned offset) in
          let accepted := lazymatch last with
          | Z0 => constr:(true) | Zpos _ => constr:(true)
          end in
          let index := eval vm_compute in (Z.to_nat ((last - first) `div` 8)) in
          let Hsum := fresh "HconstantWordAddress" in
          assert (Hsum : bv_unsigned (bv_add sp offset) = (base + last)%Z)
            by bv_solve;
          let Hindex := fresh "HconstantWordLookup" in
          assert (Hindex : Z.to_nat
            ((bv_unsigned (bv_add sp offset) - start) `div` 8) = index) by
            (rewrite Hsum; replace (base + last - start)%Z with (last - first)%Z by lia;
             reflexivity);
          rewrite Hindex in Hlookup; clear Hsum Hindex;
          rewrite ?lookup_cons ?lookup_nil in Hlookup;
          lazymatch type of Hlookup with
          | Some ?expected = Some ?actual =>
              is_var actual;
              let Hvalue := fresh "HconstantWordValue" in
              injection Hlookup as Hvalue; subst actual
          end
      end
  end.

Ltac zesu_named_frame_scratch_address :=
  zesu_call_ownership_on;
  let _ := constr:(_ : ZesuStepArrayLoadPriority) in
  lazymatch goal with
  | |- bv_unsigned ?source = (bv_unsigned ?frame - 48)%Z =>
      let head := get_head frame in
      is_const head;
      let Halias := fresh "HframeScratchAlias" in
      assert (Halias : source = (frame - BV 64 48)%bv) by
        (unfold head; bv_solve);
      rewrite Halias; unfold head; bv_solve
  end.

Lemma zesu_empty_word_array `{!islaG Sigma} (address : Z) :
  ⌜0 <= address <= 2 ^ 64⌝ ⊢ address ↦ₘ∗ ([] : list (bv 64)).
Proof.
  rewrite mem_mapsto_array_eq /mem_mapsto_array_def. cbn.
  iIntros "%Hrange". iExists 8%N.
  iSplit; [done |]. iSplit; [iPureIntro; lia | done].
Qed.

Print Assumptions zesu_empty_word_array.

Lemma zesu_simplify_empty_word_array `{!islaG Sigma} (address : Z) G :
  (⌜0 <= address <= 2 ^ 64⌝ ∗ G)%I ⊢
  simplify_goal (address ↦ₘ∗ ([] : list (bv 64))) G.
Proof.
  iIntros "[%Hrange HG]". iFrame "HG".
  iApply zesu_empty_word_array. done.
Qed.
Definition zesu_simplify_empty_word_array_inst `{!islaG Sigma}
    `{!ZesuStepCallOwnership} :=
  [instance zesu_simplify_empty_word_array with 0%N].
#[export] Existing Instance zesu_simplify_empty_word_array_inst | 0.
Print Assumptions zesu_simplify_empty_word_array.
