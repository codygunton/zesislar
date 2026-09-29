Require Import ZesuSsz.Automation.All.
Require Import isla.riscv64.riscv64.
From Coq Require Import Lia.

Lemma exact_tail_boolean_bytes_scratch_handoff `{!islaG Sigma}
    (sp : bv 64) (P : iProp Sigma) :
  (bv_unsigned sp - 48) ↦ₘ? 32 ∗
  (bv_unsigned sp - 16) ↦ₘ? 16 ∗ P -∗
  (bv_unsigned sp - 48) ↦ₘ? 48 ∗ P.
Proof.
  iIntros "(Hprefix & Hsuffix & HP)". iFrame "HP".
  iApply (mem_mapsto_uninit_combine 32 with "Hprefix [Hsuffix]"); first lia.
  replace (bv_unsigned sp - 48 + 32)%Z with (bv_unsigned sp - 16)%Z by lia.
  iExact "Hsuffix".
Qed.
Print Assumptions exact_tail_boolean_bytes_scratch_handoff.

Lemma exact_tail_scalar_scratch_handoff `{!islaG Sigma}
    (sp old : bv 64) (P : iProp Sigma) :
  (bv_unsigned sp - 16) ↦ₘ old ∗
  (bv_unsigned sp - 8) ↦ₘ? 8 ∗ P -∗
  (bv_unsigned sp - 16) ↦ₘ? 16 ∗ P.
Proof.
  iIntros "(Hword & Hsuffix & HP)". iFrame "HP".
  iDestruct (mem_mapsto_mapsto_to_uninit with "Hword") as "Hprefix".
  iApply (mem_mapsto_uninit_combine 8 with "Hprefix [Hsuffix]"); first lia.
  replace (bv_unsigned sp - 16 + 8)%Z with (bv_unsigned sp - 8)%Z by lia.
  iExact "Hsuffix".
Qed.
Print Assumptions exact_tail_scalar_scratch_handoff.
