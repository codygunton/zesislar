From Coq Require Import Lists.List ZArith.ZArith.
Require Import isla.riscv64.riscv64.
From IslaTraces.write_success_02 Require Import instrs.
From IslaTraces.write_success_01 Require Import instrs.
Require Import ZesuSsz.Contracts.IslarisMemory.
Require Import ZesuSsz.Contracts.IslarisMachine.
Require Import ZesuSsz.Experiments.WriteSuccessEvents.
Require Import ZesuSsz.Experiments.WriteSuccessMemcpy.

(** Standard ABI adapters for the shared output and memory-copy helpers. *)

Require Import ZesuSsz.Experiments.WriteSuccessCallAbi.
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
  ([∗ list] instruction ∈ IslaTraces.write_success_02.instrs.instr_map,
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
  ([∗ list] instruction ∈ IslaTraces.write_success_02.instrs.instr_map,
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

Definition zesuMemcpyCallSpec `{!islaG Sigma} `{!threadG} : iProp Sigma :=
  (zesu_c_call 0
    (fun args _ RET =>
      ∃ srcdata : list (bv 8),
      bv_unsigned (args !!! 1%nat) ↦ₘ∗ srcdata ∗
      bv_unsigned (args !!! 0%nat) ↦ₘ? bv_unsigned (args !!! 2%nat) ∗
      ⌜bv_unsigned (args !!! 2%nat) <= length srcdata⌝ ∗
      ⌜0x20000000 <= bv_unsigned (args !!! 1%nat)⌝ ∗
      ⌜bv_unsigned (args !!! 1%nat) + bv_unsigned (args !!! 2%nat) <
        0x40000000⌝ ∗
      ⌜0x20000000 <= bv_unsigned (args !!! 0%nat)⌝ ∗
      ⌜bv_unsigned (args !!! 0%nat) + bv_unsigned (args !!! 2%nat) <
        0x40000000⌝ ∗
      RET (fun _ =>
        bv_unsigned (args !!! 1%nat) ↦ₘ∗ srcdata ∗
        bv_unsigned (args !!! 0%nat) ↦ₘ∗
          take (Z.to_nat (bv_unsigned (args !!! 2%nat))) srcdata ∗ True)))%I.

Global Instance : LithiumUnfold (@zesuMemcpyCallSpec) := I.

Lemma zesu_memcpy_call_correct `{!islaG Sigma} `{!threadG} :
  ([∗ list] instruction ∈ IslaTraces.write_success_02.instrs.instr_map,
    instr instruction.1 (Some instruction.2))%I -∗
  instr_body 0x101d4 zesuMemcpyCallSpec.
Proof.
  iStartProof. iIntros "#Hcode".
  rewrite instr_pre'_eq. iIntros "Hspec".
  iEval (unfold zesuMemcpyCallSpec, zesu_c_call) in "Hspec".
  iDestruct "Hspec" as (sp ret) "(Hsys & Htmp & Hrest)".
  iEval (rewrite reg_mapsto_pred_eq /reg_mapsto_pred_def) in "Hrest".
  iDestruct "Hrest" as (r10) "(H10 & Hrest)".
  iDestruct "Hrest" as (b10) "[%Hb10 Hrest]". subst r10.
  iDestruct "Hrest" as (r11) "[H11 Hrest]".
  iDestruct "Hrest" as (b11) "[%Hb11 Hrest]". subst r11.
  iDestruct "Hrest" as (r12) "[H12 Hrest]".
  iDestruct "Hrest" as (b12) "[%Hb12 Hrest]". subst r12.
  iDestruct "Hrest" as (r13) "[H13 Hrest]".
  iDestruct "Hrest" as (b13) "[%Hb13 Hrest]". subst r13.
  iDestruct "Hrest" as (r14) "[H14 Hrest]".
  iDestruct "Hrest" as (b14) "[%Hb14 Hrest]". subst r14.
  iDestruct "Hrest" as (r15) "[H15 Hrest]".
  iDestruct "Hrest" as (b15) "[%Hb15 Hrest]". subst r15.
  iDestruct "Hrest" as (r16) "[H16 Hrest]".
  iDestruct "Hrest" as (b16) "[%Hb16 Hrest]". subst r16.
  iDestruct "Hrest" as (r17) "[H17 Hrest]".
  iDestruct "Hrest" as (b17) "[%Hb17 Hrest]". subst r17.
  iDestruct "Hrest" as (r8) "(H8 & %Hr8 & Hrest)".
  iDestruct "Hrest" as (r9) "(H9 & %Hr9 & Hrest)".
  iDestruct "Hrest" as (r18) "(H18 & %Hr18 & Hrest)".
  iDestruct "Hrest" as (r19) "(H19 & %Hr19 & Hrest)".
  iDestruct "Hrest" as (r20) "(H20 & %Hr20 & Hrest)".
  iDestruct "Hrest" as (r21) "(H21 & %Hr21 & Hrest)".
  iDestruct "Hrest" as (r22) "(H22 & %Hr22 & Hrest)".
  iDestruct "Hrest" as (r23) "(H23 & %Hr23 & Hrest)".
  iDestruct "Hrest" as (r24) "(H24 & %Hr24 & Hrest)".
  iDestruct "Hrest" as (r25) "(H25 & %Hr25 & Hrest)".
  iDestruct "Hrest" as (r26) "(H26 & %Hr26 & Hrest)".
  iDestruct "Hrest" as (r27) "(H27 & %Hr27 & Hrest)".
  iDestruct "Hrest" as
    "(H1 & H2 & %Hspalign & %Hret0 & %Hret1 & %Hret2 &
      %Hstackbounds & Hstack & Hrest)".
  iDestruct "Hrest" as (srcdata)
    "(Hsrc & Hdst & %Hcount & %Hsrcmin & %Hsrcmax &
      %Hdstmin & %Hdstmax & Hret)".
  simpl in Hcount, Hsrcmin, Hsrcmax, Hdstmin, Hdstmax.
  iEval (simpl) in "Hsrc".
  iEval (simpl) in "Hdst".
  iEval (simpl) in "Hret".
  set (count := Z.to_nat (bv_unsigned b12)).
  have HcountNat : (count <= length srcdata)%nat.
  { subst count. apply Nat2Z.inj_le. rewrite Z2Nat.id;
      [exact Hcount | bv_solve]. }
  iDestruct (mem_mapsto_array_app 8%N (bv_unsigned b11) (DfracOwn 1)
    (take count srcdata) (drop count srcdata) with "[Hsrc]") as
    "[Hsrc Hsuffix]".
  { rewrite take_drop. iExact "Hsrc". }
  iDestruct (mem_mapsto_uninit_to_byte_array with "Hdst") as
    (dstdata Hdstlen) "Hdst".
  have Htake : length (take count srcdata) = count.
  { rewrite length_take. lia. }
  iEval (rewrite Htake) in "Hsuffix".
  set (P := (
    (bv_unsigned b11 + Z.of_N (8 `div` 8) * count) ↦ₘ∗
      drop count srcdata ∗
    reg_col ((fun r => (KindReg r, BitsShape 64)) <$> tmp_registers) ∗
    "x16" ↦ᵣ RVal_Bits b16 ∗ "x17" ↦ᵣ RVal_Bits b17 ∗
    "x8" ↦ᵣ r8 ∗ "x9" ↦ᵣ r9 ∗
    "x18" ↦ᵣ r18 ∗ "x19" ↦ᵣ r19 ∗ "x20" ↦ᵣ r20 ∗
    "x21" ↦ᵣ r21 ∗ "x22" ↦ᵣ r22 ∗ "x23" ↦ᵣ r23 ∗
    "x24" ↦ᵣ r24 ∗ "x25" ↦ᵣ r25 ∗ "x26" ↦ᵣ r26 ∗
    "x27" ↦ᵣ r27 ∗ "x2" ↦ᵣ RVal_Bits sp ∗
    (bv_unsigned sp - 0) ↦ₘ? 0 ∗ True)%I).
  iPoseProof (zesu_memcpy_correct b10 b11 b12 ret
    (take count srcdata) dstdata P with "Hcode") as "Hbody".
  rewrite instr_pre'_eq. iApply "Hbody".
  iExists b13, b14, b15.
  iFrame "Hsys H1 H10 H11 H12 H13 H14 H15 Hsrc Hdst".
  repeat iSplit; try iPureIntro; try assumption; try lia.
  iSplitL "Hret".
  - rewrite instr_pre'_eq. iNext. iIntros "Hpost".
    iApply "Hret".
    iDestruct "Hpost" as (final13 final14)
      "(Hsys & H1 & H10 & H11 & H12 & H13 & H14 & H15 &
        Hsrc & Hdst & HP & _)".
    subst P.
    iDestruct "HP" as
      "(Hsuffix & Htmp & H16 & H17 & H8 & H9 & H18 & H19 & H20 &
        H21 & H22 & H23 & H24 & H25 & H26 & H27 & H2 & Hstack & _)".
    iPoseProof (mem_mapsto_array_app_combine_at 8%N (bv_unsigned b11)
      (DfracOwn 1) (take count srcdata) (drop count srcdata) count Htake
      with "Hsrc Hsuffix") as "Hsrc".
    iEval (rewrite take_drop) in "Hsrc".
    liARun.
  - subst P. iFrame.
Qed.

Lemma zesu_memcpy_call_pre `{!islaG Sigma} `{!threadG} :
  ([∗ list] instruction ∈ IslaTraces.write_success_02.instrs.instr_map,
    instr instruction.1 (Some instruction.2))%I -∗
  □ instr_pre 0x101d4 zesuMemcpyCallSpec.
Proof.
  iStartProof. iIntros "#Hcode". iModIntro.
  iApply instr_pre_to_body. iNext.
  iApply zesu_memcpy_call_correct. iExact "Hcode".
Qed.

Definition zesuWriteOutputCallSpec `{!islaG Sigma} `{!threadG} : iProp Sigma :=
  (zesu_c_call 0
    (fun args _ RET =>
      ∃ tail : spec,
      mmio_range 0x2401a0c0 16 ∗
      spec_trace (writeOutputEvents (args !!! 0%nat) (args !!! 1%nat) tail) ∗
      RET (fun _ =>
        mmio_range 0x2401a0c0 16 ∗ spec_trace tail ∗ True)))%I.

Global Instance : LithiumUnfold (@zesuWriteOutputCallSpec) := I.

Lemma zesu_write_output_call_correct `{!islaG Sigma} `{!threadG} :
  ([∗ list] instruction ∈ IslaTraces.write_success_01.instrs.instr_map,
    instr instruction.1 (Some instruction.2))%I -∗
  instr_body 0x10190 zesuWriteOutputCallSpec.
Proof.
  move => * /=.
  iStartProof.
  liARun.
  Unshelve. all: prepare_sidecond.
  all: try assumption.
  all: try bv_solve.
  all: lazymatch goal with |- ?G => fail "side condition" G end.
Qed.

Lemma zesu_write_output_call_pre `{!islaG Sigma} `{!threadG} :
  ([∗ list] instruction ∈ IslaTraces.write_success_01.instrs.instr_map,
    instr instruction.1 (Some instruction.2))%I -∗
  □ instr_pre 0x10190 zesuWriteOutputCallSpec.
Proof.
  iStartProof. iIntros "#Hcode". iModIntro.
  iApply instr_pre_to_body. iNext.
  iApply zesu_write_output_call_correct. iExact "Hcode".
Qed.
