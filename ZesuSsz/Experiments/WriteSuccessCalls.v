From Coq Require Import Lists.List ZArith.ZArith.
Require Import isla.riscv64.riscv64.
From IslaTraces.write_success_15 Require Import instrs.
Require Import ZesuSsz.Contracts.IslarisMemory.
Require Import ZesuSsz.Contracts.IslarisMachine.
Require Import ZesuSsz.Experiments.WriteSuccess.

Definition zesuMemcpyPublicSpec `{!islaG Sigma} `{!threadG}
    (dst src n ret : bv 64) (srcdata : list (bv 8)) : iProp Sigma :=
  (∃ (tmp13 tmp14 tmp15 : bv 64),
    reg_col zesu_ram_sys_regs ∗
    "x1" ↦ᵣ RVal_Bits ret ∗
    "x10" ↦ᵣ RVal_Bits dst ∗ "x11" ↦ᵣ RVal_Bits src ∗
    "x12" ↦ᵣ RVal_Bits n ∗ "x13" ↦ᵣ RVal_Bits tmp13 ∗
    "x14" ↦ᵣ RVal_Bits tmp14 ∗ "x15" ↦ᵣ RVal_Bits tmp15 ∗
    bv_unsigned src ↦ₘ∗ srcdata ∗
    bv_unsigned dst ↦ₘ? Z.of_nat (length srcdata) ∗
    ⌜bv_unsigned n = length srcdata⌝ ∗
    ⌜(0x20000000 <= bv_unsigned src)%Z⌝ ∗
    ⌜(bv_unsigned src + bv_unsigned n < 0x40000000)%Z⌝ ∗
    ⌜(0x20000000 <= bv_unsigned dst)%Z⌝ ∗
    ⌜(bv_unsigned dst + bv_unsigned n < 0x40000000)%Z⌝ ∗
    ⌜bv_extract 0 1 ret = BV 1 0⌝ ∗
    ⌜bv_extract 1 1 ret = BV 1 0⌝ ∗
    ⌜bv_extract 0 2 ret = BV 2 0⌝ ∗
    instr_pre (bv_unsigned ret)
      (∃ (final13 final14 : bv 64),
        reg_col zesu_ram_sys_regs ∗
        "x1" ↦ᵣ RVal_Bits ret ∗
        "x10" ↦ᵣ RVal_Bits dst ∗ "x11" ↦ᵣ RVal_Bits src ∗
        "x12" ↦ᵣ RVal_Bits n ∗ "x13" ↦ᵣ RVal_Bits final13 ∗
        "x14" ↦ᵣ RVal_Bits final14 ∗ "x15" ↦ᵣ RVal_Bits n ∗
        bv_unsigned src ↦ₘ∗ srcdata ∗ bv_unsigned dst ↦ₘ∗ srcdata ∗
        True) ∗ True)%I.

Global Instance : LithiumUnfold (@zesuMemcpyPublicSpec) := I.

Lemma zesu_memcpy_public_correct `{!islaG Sigma} `{!threadG}
    (dst src n ret : bv 64) (srcdata : list (bv 8)) :
  ([∗ list] instruction ∈ IslaTraces.write_success_15.instrs.instr_map,
    instr instruction.1 (Some instruction.2))%I -∗
  instr_body 0x101d4 (zesuMemcpyPublicSpec dst src n ret srcdata).
Proof.
  iStartProof. iIntros "#Hcode".
  rewrite instr_pre'_eq. iIntros "Hspec".
  iDestruct "Hspec" as
    (tmp13 tmp14 tmp15) "(Hregs & H1 & H10 & H11 & H12 & H13 & H14 & H15 &
      Hsrc & Hdst & %Hlen & %Hsrcmin & %Hsrcmax & %Hdstmin & %Hdstmax &
      %Hret0 & %Hret1 & %Hret2 & Hret & _)".
  iDestruct (mem_mapsto_uninit_to_byte_array with "Hdst") as
    (dstdata Hdstlen) "Hdst".
  iPoseProof (zesu_memcpy_correct dst src n ret srcdata dstdata True%I
    with "Hcode") as "Hbody".
  rewrite instr_pre'_eq. iApply ("Hbody" with "[-]").
  iExists tmp13, tmp14, tmp15. iFrame.
  repeat iSplit; try iPureIntro; try assumption; try lia.
  rewrite instr_pre'_eq. iNext. iIntros "Hpost". iApply "Hret".
  iDestruct "Hpost" as (final13 final14) "Hpost".
  iDestruct "Hpost" as
    "(Hregs & H1 & H10 & H11 & H12 & H13 & H14 & H15 & Hsrc & Hdst & _ & _)".
  iExists final13, final14. iFrame.
Qed.

Definition zesuMemcpyAny `{!islaG Sigma} `{!threadG} : iProp Sigma :=
  (∃ (dst src ret : bv 64) (srcdata : list (bv 8)),
    zesuMemcpyPublicSpec dst src (Z_to_bv 64 (length srcdata)) ret srcdata)%I.

Global Instance : LithiumUnfold (@zesuMemcpyAny) := I.

Lemma zesu_memcpy_any_pre `{!islaG Sigma} `{!threadG} :
  ([∗ list] instruction ∈ IslaTraces.write_success_15.instrs.instr_map,
    instr instruction.1 (Some instruction.2))%I -∗
  □ instr_pre 0x101d4 zesuMemcpyAny.
Proof.
  iStartProof. iIntros "#Hcode". iModIntro.
  iApply instr_pre_to_body. iNext.
  rewrite instr_pre'_eq. iIntros "Hspec".
  iDestruct "Hspec" as (dst src ret srcdata) "Hspec".
  iPoseProof (zesu_memcpy_public_correct dst src
    (Z_to_bv 64 (length srcdata)) ret srcdata with "Hcode") as "Hbody".
  rewrite instr_pre'_eq. iApply ("Hbody" with "Hspec").
Qed.
