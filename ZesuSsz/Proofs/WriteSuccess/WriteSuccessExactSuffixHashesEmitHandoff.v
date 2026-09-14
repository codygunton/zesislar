Require Import ZesuSsz.Automation.All.
Require Import ZesuSsz.Automation.WordArrays.
Import WordMatching.
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Export.Snapshots.
From ZesuSsz.Proofs.WriteSuccess Require Import
  WriteSuccessExactSuffixHashesWord0 WriteSuccessExactSuffixHashesWordHandoffs
  WriteSuccessExactSuffixHashesEmit WriteSuccessExactSuffixHashesPayloadWords.

Definition suffixWordRegisterShapes : list (reg_kind * valu_shape) :=
  (fun r => (KindReg r, BitsShape 64)) <$>
    ["x10";"x11";"x12";"x13";"x14";"x15";"x16"].

Definition suffixOutputResources `{!islaG Sigma} `{!threadG}
    (sp old_ra old5 : bv 64) (row : list (bv 8)) (tail : spec)
    (P : iProp Sigma) : iProp Sigma :=
  ("x1" ↦ᵣ RVal_Bits old_ra ∗ "x5" ↦ᵣ RVal_Bits old5 ∗
   mmio_range 0x2401a0c0 16 ∗
   spec_trace (writeOutputEvents (sp + BV 64 1744)%bv (BV 64 32) row tail) ∗ P ∗ True)%I.
Global Instance : LithiumUnfold (@suffixOutputResources) := I.

Definition suffixEmitCallerFrame `{!islaG Sigma} `{!threadG}
    (sp pointer : bv 64) (base : Z) (source : list (bv 8)) (index : nat)
    (P : iProp Sigma) : iProp Sigma :=
  ("x9" ↦ᵣ RVal_Bits pointer ∗
   reg_col ((fun r => (KindReg r, BitsShape 64)) <$> ["x12";"x13";"x14";"x15";"x16"]) ∗
   base ↦ₘ∗ source ∗ ⌜bv_unsigned pointer = (base + Z.of_nat index)%Z⌝ ∗
   ⌜(index + 32 <= length source)%nat⌝ ∗ ⌜(0x20000000 <= base)%Z⌝ ∗
   ⌜(base + Z.of_nat (length source) < 0x40000000)%Z⌝ ∗
   ⌜bv_unsigned sp `mod` 8 = 0⌝ ∗ ⌜(0x20000000 <= bv_unsigned sp)%Z⌝ ∗
   ⌜(bv_unsigned sp + 1776 < 0x40000000)%Z⌝ ∗ P ∗ True)%I.
Global Instance : LithiumUnfold (@suffixEmitCallerFrame) := I.

Lemma suffix_words_to_emit `{!islaG Sigma} `{!threadG}
    sp pointer base source index old_ra old5 tail (P : iProp Sigma) :
  suffixWord0Post sp pointer base source index (suffixWordFrame0 sp source index
    (suffixOutputResources sp old_ra old5 (take 32 (drop index source)) tail P)) -∗
  ∃ old_data old_size : bv 64,
    suffixEmitEntry sp old_ra old5 old_data old_size (take 32 (drop index source)) tail
      (suffixEmitCallerFrame sp pointer base source index P).
Proof.
  unfold suffixWord0Post, suffixWordFrame0, suffixOutputResources.
  iIntros "(Hsys & Hsp & Hptr & Hregs & Hsource & H0 & %Hcursor & %Hbound & %Hbase & %Hend & %Halign & %Hlow & %Hhigh & Hframe & _)".
  iDestruct "Hframe" as "(H1 & H2 & H3 & %Hwhole & Houtput & _)".
  iDestruct "Houtput" as "(Hra & H5 & Hmmio & Htrace & HP & _)".
  iDestruct (reg_col_lookup suffixWordRegisterShapes
    0 (KindReg "x10", BitsShape 64) ltac:(vm_compute; reflexivity) with "Hregs") as (v10 Hv10) "(H10 & Hregs)".
  iDestruct (reg_col_lookup (list_delete 0%nat suffixWordRegisterShapes)
    0 (KindReg "x11", BitsShape 64) ltac:(vm_compute; reflexivity) with "Hregs") as (v11 Hv11) "(H11 & Hregs)".
  destruct (valu_has_bits_shape _ _ Hv10) as [old_data ->].
  destruct (valu_has_bits_shape _ _ Hv11) as [old_size ->].
  have Hrow : length (take 32 (drop index source)) = 32%nat by rewrite length_take length_drop; lia.
  have Haddress : bv_unsigned (sp + BV 64 1744)%bv = (bv_unsigned sp + 1744)%Z by clear -Hlow Hwhole; bv_solve.
  iAssert (∃ _ : unit, (bv_unsigned sp + 1744) ↦ₘ∗ take 32 (drop index source) ∗ True)%I with "[H0 H1 H2 H3]" as "Hrow".
  { iAssert ((bv_unsigned sp + 1744) ↦ₘ Z_to_bv 64 (little_endian_to_bv 8 (take 8 (drop 0 (take 32 (drop index source))))))%I with "[H0]" as "H0".
    { rewrite (suffix_row_word source index 0 ltac:(lia)). iExact "H0". }
    iAssert ((bv_unsigned sp + 1752) ↦ₘ Z_to_bv 64 (little_endian_to_bv 8 (take 8 (drop 8 (take 32 (drop index source))))))%I with "[H1]" as "H1".
    { rewrite (suffix_row_word source index 8 ltac:(lia)). iExact "H1". }
    iAssert ((bv_unsigned sp + 1760) ↦ₘ Z_to_bv 64 (little_endian_to_bv 8 (take 8 (drop 16 (take 32 (drop index source))))))%I with "[H2]" as "H2".
    { rewrite (suffix_row_word source index 16 ltac:(lia)). iExact "H2". }
    iAssert ((bv_unsigned sp + 1768) ↦ₘ Z_to_bv 64 (little_endian_to_bv 8 (take 8 (drop 24 (take 32 (drop index source))))))%I with "[H3]" as "H3".
    { rewrite (suffix_row_word source index 24 ltac:(lia)). iExact "H3". }
    zesu_run. }
  iDestruct "Hrow" as (_) "[Hrow _]". iEval (rewrite -Haddress) in "Hrow".
  iExists old_data, old_size. unfold suffixEmitEntry, suffixEmitFrame, suffixEmitCallerFrame.
  iFrame. repeat iSplit; done.
Qed.
Print Assumptions suffix_words_to_emit.
