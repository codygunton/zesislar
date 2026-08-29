From Coq Require Import Lists.List ZArith.ZArith.
Require Import isla.riscv64.riscv64.
From IslaTraces.write_success_monolithic_00 Require Import instrs.
From IslaTraces.write_success_monolithic_01 Require Import instrs.
From IslaTraces.write_success_monolithic_02 Require Import instrs.
From IslaTraces.write_success_monolithic_03 Require Import instrs.
Require Import ZesuSsz.Contracts.IslarisMachine.

Import ListNotations.

Definition writeSuccessMonolithicOtherRegisters : list string :=
  ["x3"; "x4"; "x5"; "x6"; "x7"; "x13"; "x14"; "x15"; "x16"; "x17";
   "x28"; "x29"; "x30"; "x31"].

Definition writeSuccessMonolithicOtherRegShapes : list (reg_kind * valu_shape) :=
  (fun register => (KindReg register, BitsShape 64))
    <$> writeSuccessMonolithicOtherRegisters.

Definition writeSuccessMonolithicOutputEvents
    (data size : bv 64) (tail : spec) : spec :=
  scons (SWriteMem (BV 64 0x2401a0c0) data)
    (scons (SWriteMem (BV 64 0x2401a0c8) size) tail).

Definition writeSuccessMemcpyLoop `{!islaG Sigma} `{!threadG} : iProp Sigma :=
  ∃ (tmp13 tmp14 src dst n ret i : bv 64)
    (srcdata dstdata : list (bv 8)) (P : iProp Sigma),
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
      P ∗ True) ∗ P ∗ True.

Global Instance : LithiumUnfold (@writeSuccessMemcpyLoop) := I.

(** This deliberately uses one [instr_body] and one automation run.  It does
    not import, state, or apply contracts for any callee.  [Abort] keeps the
    first direct-search result visible without presenting it as a proof. *)
Lemma write_success_monolithic_attempt `{!islaG Sigma} `{!threadG}
    (sp decoded ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : bv 64)
    (decodedBytes : list (bv 8)) (tail : spec) :
  ([∗ list] instruction ∈
      IslaTraces.write_success_monolithic_00.instrs.instr_map,
    instr instruction.1 (Some instruction.2))%I -∗
  ([∗ list] instruction ∈
      IslaTraces.write_success_monolithic_01.instrs.instr_map,
    instr instruction.1 (Some instruction.2))%I -∗
  ([∗ list] instruction ∈
      IslaTraces.write_success_monolithic_02.instrs.instr_map,
    instr instruction.1 (Some instruction.2))%I -∗
  ([∗ list] instruction ∈
      IslaTraces.write_success_monolithic_03.instrs.instr_map,
    instr instruction.1 (Some instruction.2))%I -∗
  instr_body 0x14d30 (
    reg_col zesu_ram_sys_regs ∗
    reg_col writeSuccessMonolithicOtherRegShapes ∗
    "x1" ↦ᵣ RVal_Bits ra ∗ "x2" ↦ᵣ RVal_Bits sp ∗
    "x8" ↦ᵣ RVal_Bits s0 ∗ "x9" ↦ᵣ RVal_Bits s1 ∗
    "x18" ↦ᵣ RVal_Bits s2 ∗ "x19" ↦ᵣ RVal_Bits s3 ∗
    "x20" ↦ᵣ RVal_Bits s4 ∗ "x21" ↦ᵣ RVal_Bits s5 ∗
    "x22" ↦ᵣ RVal_Bits s6 ∗ "x23" ↦ᵣ RVal_Bits s7 ∗
    "x24" ↦ᵣ RVal_Bits s8 ∗ "x25" ↦ᵣ RVal_Bits s9 ∗
    "x26" ↦ᵣ RVal_Bits s10 ∗ "x27" ↦ᵣ RVal_Bits s11 ∗
    "x10" ↦ᵣ RVal_Bits decoded ∗ "x11" ↦ᵣ: (fun _ =>
    "x12" ↦ᵣ: (fun _ =>
    (bv_unsigned sp - 0x7d0) ↦ₘ? 2000 ∗
    bv_unsigned decoded ↦ₘ∗ decodedBytes ∗
    mmio_range 0x2401a0c0 16 ∗
    spec_trace
      (writeSuccessMonolithicOutputEvents
        (BV 64 0x179c5) (BV 64 6) tail) ∗
    ⌜bv_extract 0 4 sp = BV 4 0⌝ ∗
    ⌜(0x20000800 <= bv_unsigned sp)%Z⌝ ∗
    ⌜(bv_unsigned sp + 0x800 < 0x40000000)%Z⌝ ∗
    ⌜bv_extract 0 3 decoded = BV 3 0⌝ ∗
    ⌜length decodedBytes = 848%nat⌝ ∗
    ⌜(0x20000000 <= bv_unsigned decoded)%Z⌝ ∗
    ⌜(bv_unsigned decoded + 848 < 0x40000000)%Z⌝ ∗
    instr_pre 0x14d10 True ∗ True)))%I.
Proof.
  iStartProof.
  iIntros "#H00 #H01 #H02 #H03".
  iEval (simpl) in "H01".
  iDestruct "H01" as
    "(#H101d4 & #H101d8 & #H101dc & #H101e0 & #H101e4 & #H101e8 &
     #H101ec & #H101f0 & #H101f4 & _)".
  iAssert (□ instr_pre 0x101d8 writeSuccessMemcpyLoop)%I as "#Hmemcpy".
  { iLöb as "IH".
    iModIntro.
    iApply instr_pre_to_body.
    iNext.
    iPoseProof "IH" as "#Hloop".
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
      { apply Nat2Z.inj_lt. rewrite Z2Nat.id;
          [rewrite <- H0; exact Hiz | bv_solve]. }
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
          dstdata, srcdata, tt)ₗ.
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
    { rewrite (take_ge dstdata) in H7; [|bv_solve].
      rewrite (take_ge srcdata) in H7; [|bv_solve].
      exact H7. }
    { replace (Z.to_nat (bv_unsigned (i + 1))) with
        (S (Z.to_nat (bv_unsigned i))) by bv_solve.
      erewrite take_S_r. 2: {
        erewrite <- list_lookup_insert; do 2 f_equal; bv_solve. }
      erewrite take_S_r. 2: exact Hsrcbyte.
      rewrite take_insert; [|bv_solve].
      f_equal; [done |]. f_equal. bv_solve. } }
  (* A direct [liARun] does not reshape the 848-byte source and 2000-byte
     stack resources to the 720-byte loop invariant.  It therefore expands
     the loop instead of applying [Hmemcpy]. *)
Abort.
