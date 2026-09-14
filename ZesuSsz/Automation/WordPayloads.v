Require Import ZesuSsz.Automation.All.
Require Import ZesuSsz.Contracts.IslarisMemory.
Require Import isla.riscv64.riscv64.
From Coq Require Import Lists.List ZArith.ZArith.

Definition words_20_payload (first second : bv 64) (last : bv 32) : list (bv 8) :=
  bv_to_little_endian 8 8 (bv_unsigned first) ++
  bv_to_little_endian 8 8 (bv_unsigned second) ++
  bv_to_little_endian 4 8 (bv_unsigned last).

Lemma words_20_payload_merge `{!islaG Sigma}
    (a : Z) (first second : bv 64) (last : bv 32) :
  (a ↦ₘ first ∗ (a + 8) ↦ₘ second ∗ (a + 16) ↦ₘ last ∗ True)%I -∗
  a ↦ₘ∗ words_20_payload first second last.
Proof.
  iIntros "(Hfirst & Hsecond & Hlast & _)".
  iDestruct (mem_mapsto_mapsto_to_byte_array_N 8 with "Hfirst") as "Hfirst".
  iDestruct (mem_mapsto_mapsto_to_byte_array_N 8 with "Hsecond") as "Hsecond".
  iDestruct (mem_mapsto_mapsto_to_byte_array_N 4 with "Hlast") as "Hlast".
  unfold words_20_payload.
  iApply (mem_mapsto_array_app_combine_at 8 a (DfracOwn 1) _ _ 8 with "Hfirst").
  { rewrite length_bv_to_little_endian; done. }
  cbn. replace (a + 1 * 8)%Z with (a + 8)%Z by lia.
  iApply (mem_mapsto_array_app_combine_at 8 (a + 8) (DfracOwn 1) _ _ 8 with "Hsecond").
  { rewrite length_bv_to_little_endian; done. }
  cbn. replace (a + 8 + 1 * 8)%Z with (a + 16)%Z by lia.
  iExact "Hlast".
Qed.
Print Assumptions words_20_payload_merge.
