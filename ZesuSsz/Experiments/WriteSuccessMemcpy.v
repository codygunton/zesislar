From Coq Require Import Lists.List ZArith.ZArith.
Require Import isla.riscv64.riscv64.
From IslaTraces.write_success_02 Require Import instrs.
Require Import ZesuSsz.Contracts.IslarisMachine.
Require Import ZesuSsz.Experiments.WriteSuccessBitvector.

Import ListNotations.

#[local] Hint Rewrite bv_sign_extend_64_idemp : isla_coq_rewrite.

Definition zesuMemcpyLoopSpec `{!islaG Sigma} `{!threadG} : iProp Sigma :=
  ∃ (tmp13 tmp14 src dst n ret i : bv 64) (srcdata dstdata : list (bv 8))
    (P : iProp Sigma),
  reg_col zesu_ram_sys_regs ∗
  "x1" ↦ᵣ RVal_Bits ret ∗
  "x10" ↦ᵣ RVal_Bits dst ∗ "x11" ↦ᵣ RVal_Bits src ∗
  "x12" ↦ᵣ RVal_Bits n ∗ "x13" ↦ᵣ RVal_Bits tmp13 ∗
  "x14" ↦ᵣ RVal_Bits tmp14 ∗ "x15" ↦ᵣ RVal_Bits i ∗
  bv_unsigned src ↦ₘ∗ srcdata ∗ bv_unsigned dst ↦ₘ∗ dstdata ∗
  ⌜bv_unsigned n = length srcdata⌝ ∗
  ⌜bv_unsigned n = length dstdata⌝ ∗
  ⌜(bv_unsigned i <= bv_unsigned n)%Z⌝ ∗
  ⌜(0x20000000 <= bv_unsigned src)%Z⌝ ∗
  ⌜(bv_unsigned src + bv_unsigned n < 0x40000000)%Z⌝ ∗
  ⌜(0x20000000 <= bv_unsigned dst)%Z⌝ ∗
  ⌜(bv_unsigned dst + bv_unsigned n < 0x40000000)%Z⌝ ∗
  ⌜take (Z.to_nat (bv_unsigned i)) dstdata =
    take (Z.to_nat (bv_unsigned i)) srcdata⌝ ∗
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
      P ∗ True) ∗
  P ∗ True.

Global Instance : LithiumUnfold (@zesuMemcpyLoopSpec) := I.

Lemma zesu_memcpy_loop `{!islaG Sigma} `{!threadG} :
  ([∗ list] instruction ∈ IslaTraces.write_success_02.instrs.instr_map,
    instr instruction.1 (Some instruction.2))%I -∗
  □ instr_pre 0x101d8 zesuMemcpyLoopSpec -∗
  instr_body 0x101d8 zesuMemcpyLoopSpec.
Proof.
  move => * /=.
  iStartProof.
  liARun.
  - liARun.
    liShow.
    replace (bv_unsigned LET6) with
      (bv_unsigned src + Z.of_nat (Z.to_nat (bv_unsigned i)))%Z by bv_solve.
    iRename select (bv_unsigned src ↦ₘ∗ srcdata)%I into "Hsrc".
    have Hine : bv_unsigned i <> bv_unsigned n.
    { intro Heq. apply H12. apply bv_eq. exact Heq. }
    have Hiz : (bv_unsigned i < bv_unsigned n)%Z by lia.
    have Hi : (Z.to_nat (bv_unsigned i) < length srcdata)%nat.
    { apply Nat2Z.inj_lt. rewrite Z2Nat.id; [rewrite <- H0; exact Hiz | bv_solve]. }
    have [srcbyte Hsrcbyte] := lookup_lt_is_Some_2 srcdata _ Hi.
    iDestruct (mem_mapsto_array_lookup_acc 8%N (bv_unsigned src)
      (Z.to_nat (bv_unsigned i)) srcdata (DfracOwn 1) 1%N srcbyte
      with "Hsrc") as "[Hsrcbyte Hsrcclose]";
      [done | exact Hsrcbyte |].
    liARun.
    iRename select
      ((bv_unsigned src + Z.to_nat (bv_unsigned i))%Z ↦ₘ srcbyte)%I
      into "HsrcbyteNow".
    iExists (P,
      <[Z.to_nat ((bv_unsigned LET15 - bv_unsigned dst) `div` 1) := LET16]>
        dstdata,
      srcdata, tt)ₗ.
    red_li_prod.
    iSplitL "Hsrcclose HsrcbyteNow".
    { have Hsrcaddr :
        (bv_unsigned src + Z.to_nat (bv_unsigned i) * 1 =
         bv_unsigned src + Z.to_nat (bv_unsigned i))%Z by lia.
      iEval (rewrite Hsrcaddr) in "Hsrcclose".
      iApply "Hsrcclose". iExact "HsrcbyteNow". }
    iFrame.
    liARun.
    iPureIntro. exact H10.
  Unshelve. all: prepare_sidecond.
  all: try assumption.
  all: try rewrite length_insert.
  all: try bv_solve.
  all: try lia.
  { rewrite (take_ge dstdata) in H7.
    2: bv_solve.
    rewrite (take_ge srcdata) in H7.
    2: bv_solve.
    exact H7. }
  { replace (Z.to_nat (bv_unsigned (i + 1))) with
      (S (Z.to_nat (bv_unsigned i))) by bv_solve.
    erewrite take_S_r. 2: {
      erewrite <- list_lookup_insert; do 2 f_equal; bv_solve. }
    erewrite take_S_r. 2: exact Hsrcbyte.
    rewrite take_insert; [|bv_solve].
    f_equal; [done|]. f_equal. bv_solve. }
Qed.

Lemma zesu_memcpy_loop_pre `{!islaG Sigma} `{!threadG} :
  ([∗ list] instruction ∈ IslaTraces.write_success_02.instrs.instr_map,
    instr instruction.1 (Some instruction.2))%I -∗
  □ instr_pre 0x101d8 zesuMemcpyLoopSpec.
Proof.
  iStartProof.
  iIntros "#Hcode".
  iLöb as "IH".
  iModIntro.
  iApply instr_pre_to_body.
  iNext.
  iApply (zesu_memcpy_loop with "Hcode IH").
Qed.

Definition zesuMemcpySpec `{!islaG Sigma} `{!threadG}
    (dst src n ret : bv 64) (srcdata dstdata : list (bv 8))
    (P : iProp Sigma) : iProp Sigma :=
  (∃ (tmp13 tmp14 tmp15 : bv 64),
    reg_col zesu_ram_sys_regs ∗
    "x1" ↦ᵣ RVal_Bits ret ∗
    "x10" ↦ᵣ RVal_Bits dst ∗ "x11" ↦ᵣ RVal_Bits src ∗
    "x12" ↦ᵣ RVal_Bits n ∗ "x13" ↦ᵣ RVal_Bits tmp13 ∗
    "x14" ↦ᵣ RVal_Bits tmp14 ∗ "x15" ↦ᵣ RVal_Bits tmp15 ∗
    bv_unsigned src ↦ₘ∗ srcdata ∗ bv_unsigned dst ↦ₘ∗ dstdata ∗
    ⌜bv_unsigned n = length srcdata⌝ ∗
    ⌜bv_unsigned n = length dstdata⌝ ∗
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
        P ∗ True) ∗
    P ∗ True)%I.

Global Instance : LithiumUnfold (@zesuMemcpySpec) := I.

Lemma zesu_memcpy_correct `{!islaG Sigma} `{!threadG}
    (dst src n ret : bv 64) (srcdata dstdata : list (bv 8))
    (P : iProp Sigma) :
  ([∗ list] instruction ∈ IslaTraces.write_success_02.instrs.instr_map,
    instr instruction.1 (Some instruction.2))%I -∗
  instr_body 0x101d4 (zesuMemcpySpec dst src n ret srcdata dstdata P).
Proof.
  iStartProof.
  iIntros "#Hcode".
  iAssert (□ instr_pre 0x101d8 zesuMemcpyLoopSpec)%I as "#Hloop".
  { iLöb as "IH".
    iModIntro.
    iApply instr_pre_to_body.
    iNext.
    iApply zesu_memcpy_loop.
    - iExact "Hcode".
    - iExact "IH". }
  iEval (simpl) in "Hcode".
  iDestruct "Hcode" as
    "(#H101d4 & #H101d8 & #H101dc & #H101e0 & #H101e4 & #H101e8 &
     #H101ec & #H101f0 & #H101f4 & _)".
  liARun.
  Unshelve. all: prepare_sidecond.
  all: try assumption.
  all: try bv_solve.
  all: try lia.
  all: lazymatch goal with |- ?G => fail "side condition" G end.
Qed.

