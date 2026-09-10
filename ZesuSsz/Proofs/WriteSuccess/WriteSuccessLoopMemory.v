Require Import ZesuSsz.Automation.All.
From Coq Require Import Lists.List ZArith.ZArith.
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Contracts.IslarisMemory.

Lemma write_success_byte_array_to_uninit `{!islaG Sigma}
    (address : Z) (values : list (bv 8)) :
  address ↦ₘ∗ values -∗ address ↦ₘ? Z.of_nat (length values).
Proof.
  rewrite mem_mapsto_array_eq /mem_mapsto_array_def
    mem_mapsto_uninit_eq /mem_mapsto_uninit_def.
  iIntros "Hvalues".
  iDestruct "Hvalues" as (len Hlen Hrange) "Hvalues".
  have Hlen' : len = 1%N by nia. subst len.
  iExists (length values). iSplit; [done |]. iSplit.
  { iPureIntro. cbn in Hrange. lia. }
  iApply (big_sepL_impl' with "Hvalues").
  { rewrite length_replicate. done. }
  iIntros "!>" (index value [] Hvalue Hunit) "Hvalue".
  rewrite mem_mapsto_eq /mem_mapsto_def.
  iDestruct "Hvalue" as (byteLen HbyteLen HbyteRange) "Hvalue".
  have HbyteLen' : byteLen = 1%nat by nia. subst byteLen.
  iEval (cbn; rewrite Z.mul_1_r) in "Hvalue".
  iDestruct "Hvalue" as "[Hvalue _]".
  iExists value.
  rewrite /= Z.add_0_r -(bv_wrap_land 8) bv_wrap_small
    ?Z_to_bv_bv_unsigned; [iExact "Hvalue" | apply bv_unsigned_in_range].
Qed.

Lemma subsume_write_success_byte_array_uninit `{!islaG Sigma}
    A address requested size (values : list (bv 8)) G :
  (⌜address = requested⌝ ∗
   ⌜Z.of_nat (length values) = size⌝ ∗ ∃ x : A, G x)
  ⊢ subsume (address ↦ₘ∗ values) (fun _ : A => requested ↦ₘ? size) G.
Proof.
  iIntros "(%Haddress & %Hsize & Hcontinue) Hvalues".
  subst requested size.
  iDestruct "Hcontinue" as (x) "Hcontinue".
  iExists x. iFrame "Hcontinue".
  iApply (write_success_byte_array_to_uninit with "Hvalues").
Qed.

Definition subsume_write_success_byte_array_uninit_inst :=
  [instance @subsume_write_success_byte_array_uninit].
Global Existing Instance subsume_write_success_byte_array_uninit_inst | 80.
