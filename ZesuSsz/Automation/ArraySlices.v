Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Contracts.IslarisMemory.
From Coq Require Import Lists.List ZArith.ZArith.

Lemma array_slice_stack_index (sp first second : bv 64) :
  bv_unsigned first <= bv_unsigned second ->
  bv_unsigned sp + bv_unsigned second < 2 ^ 64 ->
  array_region_start 8 (bv_unsigned (sp + first)%bv)
    (bv_unsigned (sp + second)%bv) =
  Z.to_nat (bv_unsigned second - bv_unsigned first).
Proof.
  intros. unfold array_region_start. cbn. rewrite Z.div_1_r.
  f_equal. bv_solve.
Qed.
Print Assumptions array_slice_stack_index.

Section exact_array.
  Context `{!islaG Sigma}.
  Lemma subsume_mem_array_exact A address n (bytes : list (bv n)) G :
    (∃ x : A, G x) ⊢
    subsume (address ↦ₘ∗ bytes) (fun _ : A => address ↦ₘ∗ bytes) G.
  Proof. iDestruct 1 as (x) "HG". iIntros "Hbytes". iExists x. iFrame. Qed.
  Definition subsume_mem_array_exact_inst := [instance subsume_mem_array_exact].

  Lemma subsume_mem_array_slice A (base address : Z) (bytes : list (bv 8))
      (start count : nat) G :
    (⌜address = (base + Z.of_nat start)%Z⌝ ∗
     ⌜(start + count <= length bytes)%nat⌝ ∗
     (base ↦ₘ∗ take start bytes -∗
      (base + Z.of_nat (start + count)) ↦ₘ∗ drop (start + count) bytes -∗
      ∃ x : A, G x))%I ⊢
    subsume (base ↦ₘ∗ bytes)
      (fun _ : A => address ↦ₘ∗ take count (drop start bytes)) G.
  Proof.
    iIntros "(%Haddress & %Hbound & Hcontinue) Hbytes".
    iDestruct (mem_mapsto_array_region 8 base (DfracOwn 1) bytes start count
      Hbound with "Hbytes") as "(Hprefix & Hslice & Hsuffix)".
    cbn. rewrite !Z.mul_1_l. rewrite Haddress.
    iDestruct ("Hcontinue" with "Hprefix Hsuffix") as (x) "HG".
    iExists x. iFrame.
  Qed.
  Definition subsume_mem_array_slice_inst := [instance subsume_mem_array_slice].
End exact_array.

Module SliceMatching.
  #[export] Remove Hints subsume_mem_array_inst : typeclass_instances.
  #[export] Existing Instance subsume_mem_array_exact_inst | 0.
  #[export] Existing Instance subsume_mem_array_slice_inst | 1.
  #[export] Existing Instance subsume_mem_array_region_inst | 2.
  #[export] Hint Rewrite array_slice_stack_index using bv_solve
    : lithium_rewrite isla_coq_rewrite.
End SliceMatching.
