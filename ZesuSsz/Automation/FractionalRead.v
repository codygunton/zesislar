Require Import isla.riscv64.riscv64.
From lithium Require Import interpreter.
From iris.algebra Require Import dfrac.
From iris.proofmode Require Import environments.
From Coq Require Import Lists.List ZArith.ZArith NArith.NArith.
Require Import ZesuSsz.Evidence.Block2Core.
Open Scope Z_scope.

(* Inactive candidate. The dispatcher selects the complete resource first. *)
Section fractional_read.
  Context `{!islaG Sigma} `{!threadG}.

  Lemma block2_wp_read_mem_fractional len n kind address value tag ann es
      (fraction : dfrac) (base : Z) (values : list (bv n)) :
    (base ↦ₘ{fraction}∗ values ∗
     ⌜n = (8 * len)%N⌝ ∗ ⌜(0 < Z.of_N len)%Z⌝ ∗
     ⌜(bv_unsigned address - base) `mod` Z.of_N len = 0⌝ ∗
     ∃ index : nat,
       ⌜Z.of_nat index = (bv_unsigned address - base) / Z.of_N len⌝ ∗
       ⌜(index < length values)%nat⌝ ∗
       (∀ stored, ⌜values !! index = Some stored⌝ -∗
         ⌜value = stored⌝ -∗ base ↦ₘ{fraction}∗ values -∗ WPasm es))
    ⊢ WPasm (ReadMem (RVal_Bits (@bv_to_bvn n value)) kind
        (RVal_Bits (@bv_to_bvn 64 address)) len tag ann :t: es).
  Proof.
    iDestruct 1 as "[Hmem [%Hwidth [%Hpositive [%Halign Hcont]]]]".
    iDestruct "Hcont" as (index Heqi Hbound) "Hcont".
    destruct (lookup_lt_is_Some_2 values index Hbound) as [stored Hlookup].
    have Hbase : base = bv_unsigned address - index * Z.of_N len.
    { rewrite Heqi Z.mul_comm -Z_div_exact_full_2; [lia|lia|done]. }
    iApply (wp_read_mem_array with "Hmem [Hcont]");
      [exact Hwidth|exact Hpositive|exact Hlookup|exact Hbase|].
    iIntros (Heq) "Hmem".
    iApply ("Hcont" with "[] [] Hmem"); done.
  Qed.
End fractional_read.

Ltac block2_fractional_read_array address width spatial continuation :=
  lazymatch spatial with
  | Esnoc ?rest _ ((?base ↦ₘ{?fraction}∗ ?values)%I) =>
      first [
        lazymatch type of values with list (bv ?element_width) =>
          ZesuSsz.Evidence.Block2Core.block2_fixed base;
          ZesuSsz.Evidence.Block2Core.block2_fixed fraction;
          ZesuSsz.Evidence.Block2Core.block2_fixed values;
          constr_eq element_width width;
          let range := fresh "HreadArrayRange" in
          assert (range :
            ((base <= bv_unsigned address <
              base + Z.of_nat (length values) * Z.of_N (width `div` 8))%Z
             \/ base = bv_unsigned address)) by
            (first [right; reflexivity | left; bv_solve]);
          clear range;
          continuation fraction base values
        end
      | block2_fractional_read_array address width rest continuation ]
  | Esnoc ?rest _ _ =>
      block2_fractional_read_array address width rest continuation
  end.

Ltac block2_fractional_read_step :=
  lazymatch goal with
  | |- envs_entails ?proof_context
      (WPasm (ReadMem (RVal_Bits (@bv_to_bvn ?width ?value)) ?kind
        (RVal_Bits (@bv_to_bvn 64 ?address)) ?len ?tag ?ann :t: ?es)) =>
      ZesuSsz.Evidence.Block2Core.block2_closed width;
      ZesuSsz.Evidence.Block2Core.block2_closed len;
      ZesuSsz.Evidence.Block2Core.block2_fixed address;
      ZesuSsz.Evidence.Block2Core.block2_fixed value;
      let expected := eval cbv in ((8 * len)%N) in
      constr_eq width expected;
      let count := eval cbv in len in
      lazymatch count with Npos _ => idtac end;
      let apply_read fraction base values :=
        notypeclasses refine (tac_fast_apply
          (block2_wp_read_mem_fractional len width kind address value tag ann es
            fraction base values) _);
        liSimpl in
      lazymatch proof_context with
        | Envs ?persistent ?spatial _ =>
            first [block2_fractional_read_array address width spatial apply_read
                  | block2_fractional_read_array address width persistent apply_read]
        | _ =>
            let expanded := eval hnf in proof_context in
            lazymatch expanded with Envs ?persistent ?spatial _ =>
              first [block2_fractional_read_array address width spatial apply_read
                    | block2_fractional_read_array address width persistent apply_read]
            end
      end
  end.
