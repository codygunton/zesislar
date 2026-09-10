From Coq Require Import Lists.List ZArith.ZArith.
Require Import isla.riscv64.riscv64.
From IslaTraces.write_success_blocks Require Import
  Index Hints101 Hints102 Hints103.
Require Import ZesuSsz.Contracts.IslarisMachine.
Require Import ZesuSsz.Contracts.IslarisCode.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessHashesLoop.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessLoopCommon.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessEncoderIntCall.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessEvents.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessSuffixHashes15744Raw.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessSuffixHashes15748Raw.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessSuffixHashes1574cCall.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessSuffixHashes15750Branch.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessSuffixHashesSourceWords.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessSuffixHashesEntryAdapter.
Require Import InstrSpecs.Lookup.

Import ListNotations.

Local Remove Hints subsume_instr_pre'_inst : typeclass_instances.
Local Existing Instance subsume_instr_pre_wand_inst | 1.

#[local] Hint Extern 7
  (FindInContext (FindInstrKind ?address ?later) FICSyntactic) =>
  let reduced := eval vm_compute in address in
  first [ constr_eq address reduced; fail 1
        | change (FindInContext (FindInstrKind reduced later) FICSyntactic);
          typeclasses eauto ] : typeclass_instances.

Lemma write_success_suffix_ram_lower_904 (sp : bv 64)
    (Hmin : 0x20000000 <= bv_unsigned sp)
    (Haddr : bv_unsigned (sp + BV 64 904)%bv = bv_unsigned sp + 904) :
    bv_unsigned (sp + BV 64 904)%bv >= bv_unsigned (BV 64 0x20000000).
Proof.
  rewrite Haddr bv_unsigned_BV. lia.
Qed.

Lemma write_success_suffix_ram_lower_912 (sp : bv 64)
    (Hmin : 0x20000000 <= bv_unsigned sp)
    (Haddr : bv_unsigned (sp + BV 64 912)%bv = bv_unsigned sp + 912) :
    bv_unsigned (sp + BV 64 912)%bv >= bv_unsigned (BV 64 0x20000000).
Proof.
  rewrite Haddr bv_unsigned_BV. lia.
Qed.

Lemma write_success_suffix_ram_upper_904 (sp : bv 64)
    (Hmax : bv_unsigned sp + 1896 < 0x40000000)
    (Haddr : bv_unsigned (sp + BV 64 904)%bv = bv_unsigned sp + 904) :
    bv_unsigned (sp + BV 64 904)%bv <=
      bv_unsigned (BV 64 0x20000000 + BV 64 0x20000000 - BV 64 8)%bv.
Proof. clear - Hmax Haddr. rewrite Haddr. bv_solve. Qed.

Lemma write_success_suffix_ram_upper_912 (sp : bv 64)
    (Hmax : bv_unsigned sp + 1896 < 0x40000000)
    (Haddr : bv_unsigned (sp + BV 64 912)%bv = bv_unsigned sp + 912) :
    bv_unsigned (sp + BV 64 912)%bv <=
      bv_unsigned (BV 64 0x20000000 + BV 64 0x20000000 - BV 64 8)%bv.
Proof. clear - Hmax Haddr. rewrite Haddr. bv_solve. Qed.

Definition writeSuccessSuffixHashesEntrySpec
    `{!islaG Sigma} `{!threadG} (P : iProp Sigma) : iProp Sigma :=
  (∃ (sp pointer : bv 64) (base : Z)
      (total processed remaining : nat) (bytes : list (bv 8))
      (tail : spec),
    reg_col zesu_ram_sys_regs ∗
    reg_col writeSuccessHashesOtherRegShapes ∗
    "x2" ↦ᵣ RVal_Bits sp ∗
    "x8" ↦ᵣ RVal_Bits (Z_to_bv 64 (Z.of_nat (S remaining))) ∗
    "x9" ↦ᵣ RVal_Bits pointer ∗
    base ↦ₘ∗ bytes ∗ writeSuccessHashesScratch sp ∗
    (bv_unsigned sp + 904) ↦ₘ pointer ∗
    (bv_unsigned sp + 912) ↦ₘ Z_to_bv 64 (Z.of_nat (S remaining)) ∗
    (bv_unsigned sp - 16) ↦ₘ? 16 ∗
    mmio_range 0x2401a0c0 16 ∗
    spec_trace
      (writeOutputEvents (sp - BV 64 16)%bv (BV 64 8)
        (writeSuccessHashesEvents sp (S remaining) tail)) ∗
    P ∗ writeSuccessFixedWidthArrayInvariant
      sp pointer base total processed remaining bytes ∗
    instr_pre 0x158e0
      (writeSuccessHashesLoopExit sp base total bytes tail P) ∗ True)%I.

Global Instance : LithiumUnfold (@writeSuccessSuffixHashesEntrySpec) := I.

Definition writeSuccessSuffixHashes15740Post
    `{!islaG Sigma} `{!threadG} (P : iProp Sigma)
    (sp pointer : bv 64) (base : Z)
    (total processed remaining : nat) (bytes : list (bv 8))
    (tail : spec) : iProp Sigma :=
  (reg_col zesu_ram_sys_regs ∗
   reg_col writeSuccessHashesOtherRegShapes ∗
   "x2" ↦ᵣ RVal_Bits sp ∗
   "x8" ↦ᵣ RVal_Bits (Z_to_bv 64 (Z.of_nat (S remaining))) ∗
   "x9" ↦ᵣ RVal_Bits pointer ∗
   base ↦ₘ∗ bytes ∗ writeSuccessHashesScratch sp ∗
   (bv_unsigned sp + 904) ↦ₘ pointer ∗
   (bv_unsigned sp + 912) ↦ₘ Z_to_bv 64 (Z.of_nat (S remaining)) ∗
   (bv_unsigned sp - 16) ↦ₘ? 16 ∗
   mmio_range 0x2401a0c0 16 ∗
   spec_trace
     (writeOutputEvents (sp - BV 64 16)%bv (BV 64 8)
       (writeSuccessHashesEvents sp (S remaining) tail)) ∗
   P ∗ writeSuccessFixedWidthArrayInvariant
     sp pointer base total processed remaining bytes ∗
   instr_pre 0x158e0
     (writeSuccessHashesLoopExit sp base total bytes tail P) ∗ True)%I.

Global Instance : LithiumUnfold (@writeSuccessSuffixHashes15740Post) := I.

Definition writeSuccessSuffixHashesAt15740Spec
    `{!islaG Sigma} `{!threadG} (P : iProp Sigma) : iProp Sigma :=
  (∃ (sp pointer : bv 64) (base : Z)
      (total processed remaining : nat) (bytes : list (bv 8))
      (tail : spec),
    reg_col zesu_ram_sys_regs ∗
    reg_col writeSuccessHashesOtherRegShapes ∗
    "x2" ↦ᵣ RVal_Bits sp ∗
    "x8" ↦ᵣ RVal_Bits (Z_to_bv 64 (Z.of_nat (S remaining))) ∗
    "x9" ↦ᵣ RVal_Bits pointer ∗
    base ↦ₘ∗ bytes ∗ writeSuccessHashesScratch sp ∗
    (bv_unsigned sp + 904) ↦ₘ pointer ∗
    (bv_unsigned sp + 912) ↦ₘ Z_to_bv 64 (Z.of_nat (S remaining)) ∗
    (bv_unsigned sp - 16) ↦ₘ? 16 ∗
    mmio_range 0x2401a0c0 16 ∗
    spec_trace
      (writeOutputEvents (sp - BV 64 16)%bv (BV 64 8)
        (writeSuccessHashesEvents sp (S remaining) tail)) ∗
    P ∗ writeSuccessFixedWidthArrayInvariant
      sp pointer base total processed remaining bytes ∗
    instr_pre 0x15744
      (writeSuccessSuffixHashes15740Post P sp pointer base total processed
        remaining bytes tail) ∗ True)%I.

Global Instance : LithiumUnfold (@writeSuccessSuffixHashesAt15740Spec) := I.

Lemma write_success_suffix_hashes_15740
    `{!islaG Sigma} `{!threadG} (P : iProp Sigma) :
  instr_lookup_resources IslaTraces.write_success_blocks.Index.lookup -∗
  IslaTraces.write_success_blocks.Index.spec_instr_resources -∗
  instr_body 0x15740 (writeSuccessSuffixHashesAt15740Spec P).
Proof.
  move => *.
  iStartProof. iIntros "_ #Hlookup #Hcode".
  iEval (unfold IslaTraces.write_success_blocks.Index.spec_instr_resources)
    in "Hcode".
  iPoseProof "Hlookup" as "#Hlookup15740".
  iEval (rewrite /instr_lookup_resources) in "Hlookup15740".
  iPoseProof ("Hlookup15740" $! 0x15740 with "[]") as "#Hinstr15740".
  { iPureIntro. rewrite IslaTraces.write_success_blocks.Index.lookup_a15740.
    done. }
  iPoseProof (IslaTraces.write_success_101.a15740_spec.a15740_spec
    0x15740 with "Hinstr15740") as "Hld912".
  rewrite instr_pre'_eq. iIntros "Hentry".
  iEval (rewrite /writeSuccessSuffixHashesAt15740Spec) in "Hentry".
  iDestruct "Hentry" as
    (sp pointer base total processed remaining bytes tail)
    "(Hsys & Hregs & H2 & H8 & H9 & Hbytes & Hscratch & H904 & H912 &
      Hstack & Hmmio & Htrace & HP & Hinvariant & Hnext & _)".
  iEval (rewrite /writeSuccessFixedWidthArrayInvariant) in "Hinvariant".
  iDestruct "Hinvariant" as
    "(%Htotal & %HbytesLength & %Hpointer & %HremainingBound & %HspAlign &
      %HspMin & %HspMax & %HbaseMin & %HbaseMax & _)".
  have H912Address :
      bv_unsigned (sp + BV 64 912)%bv = bv_unsigned sp + 912.
  { rewrite bv_add_unsigned bv_unsigned_BV.
    apply bv_wrap_small.
    pose proof (bv_unsigned_in_range 64 sp).
    unfold bv_modulus in *; cbn in *; lia. }
  have H912Align :
      bv_extract 0 3 (sp + BV 64 912)%bv = BV 3 0.
  { clear - HspAlign. bv_simplify_arith HspAlign; bv_solve. }
  have H912RamLower :
      bv_unsigned (sp + BV 64 912)%bv >=
        bv_unsigned (BV 64 0x20000000) by
    apply write_success_suffix_ram_lower_912; assumption.
  have H912RamUpper :
      bv_unsigned (sp + BV 64 912)%bv <=
        bv_unsigned (BV 64 0x20000000 + BV 64 0x20000000 - BV 64 8)%bv by
    apply write_success_suffix_ram_upper_912; assumption.
  rewrite /InstrSpecs.Specs.zesu_ld_spec /InstrSpecs.Specs.rv64_ld_spec.
  iApply "Hld912".
  iExists (Z_to_bv 64 (Z.of_nat (S remaining))), sp.
  iAssert ("x8" ↦ᵣ: (fun _ => True))%I with "[H8]" as "H8Any".
  { rewrite reg_mapsto_pred_eq /reg_mapsto_pred_def.
    iExists _. iFrame. }
  iFrame "Hsys H8Any H2 H912".
  repeat iSplit; try iPureIntro; try assumption; try bv_solve; try lia.
  iEval (rewrite -instr_pre'_eq) in "Hnext".
  iApply (instr_pre_wand with "Hnext"); first done; first reflexivity.
  iIntros "Hpost".
  iDestruct "Hpost" as
    "(HsysPost & H8Post & H2Post & H912Post & _)".
  iEval (rewrite /writeSuccessSuffixHashes15740Post).
  iExists sp, pointer, base, total, processed, remaining, bytes, tail.
  iFrame "HsysPost Hregs H2Post H8Post H9 Hbytes Hscratch H904 H912Post
    Hstack Hmmio Htrace HP".
  iEval (rewrite /writeSuccessFixedWidthArrayInvariant).
  iFrame.
  done.
Qed.

Lemma write_success_suffix_hashes_entry
    `{!islaG Sigma} `{!threadG} (P : iProp Sigma) :
  instr_lookup_resources IslaTraces.write_success_blocks.Index.lookup -∗
  IslaTraces.write_success_blocks.Index.spec_instr_resources -∗
  □ instr_pre 0x15d10 zesuEncoderIntCallSpec -∗
  □ instr_pre 0x15754 (writeSuccessHashesLoopSpec P) -∗
  instr_body 0x1573c (writeSuccessSuffixHashesEntrySpec P).
Proof.
  move => *.
  iStartProof. iIntros "_ #Hlookup #Hcode #Hint #Hloop".
  iEval (unfold IslaTraces.write_success_blocks.Index.spec_instr_resources)
    in "Hcode".
  iPoseProof "Hlookup" as "#Hlookup1573c".
  iEval (rewrite /instr_lookup_resources) in "Hlookup1573c".
  iPoseProof ("Hlookup1573c" $! 0x1573c with "[]") as "#Hinstr1573c".
  { iPureIntro. rewrite IslaTraces.write_success_blocks.Index.lookup_a1573c.
    done. }
  iEval (rewrite IslaTraces.write_success_blocks.Index.lookup_a1573c)
    in "Hinstr1573c".
  iPoseProof (IslaTraces.write_success_101.a1573c_spec.a1573c_spec
    0x1573c with "Hinstr1573c") as "Hld904".
  iPoseProof ("Hlookup1573c" $! 0x15740 with "[]") as "#Hinstr15740".
  { iPureIntro. rewrite IslaTraces.write_success_blocks.Index.lookup_a15740.
    done. }
  iPoseProof (IslaTraces.write_success_101.a15740_spec.a15740_spec
    0x15740 with "Hinstr15740") as "Hld912".
  iPoseProof ("Hlookup1573c" $! 0x15744 with "[]") as "#Hinstr15744".
  { iPureIntro. rewrite IslaTraces.write_success_blocks.Index.lookup_a15744.
    done. }
  iPoseProof ("Hlookup1573c" $! 0x15748 with "[]") as "#Hinstr15748".
  { iPureIntro. rewrite IslaTraces.write_success_blocks.Index.lookup_a15748.
    done. }
  iPoseProof ("Hlookup1573c" $! 0x15750 with "[]") as "#Hinstr15750".
  { iPureIntro. rewrite IslaTraces.write_success_blocks.Index.lookup_a15750.
    done. }
  rewrite instr_pre'_eq. iIntros "Hentry".
  iEval (rewrite /writeSuccessSuffixHashesEntrySpec) in "Hentry".
  iDestruct "Hentry" as
    (sp pointer base total processed remaining bytes tail)
    "(Hsys & Hregs & H2 & H8 & H9 & Hbytes & Hscratch & H904 & H912 &
      Hstack & Hmmio & Htrace & HP & Hinvariant & Hexit & _)".
  iEval (rewrite /writeSuccessFixedWidthArrayInvariant) in "Hinvariant".
  iDestruct "Hinvariant" as
    "(%Htotal & %HbytesLength & %Hpointer & %HremainingBound & %HspAlign &
      %HspMin & %HspMax & %HbaseMin & %HbaseMax & _)".
  have H904Address :
      bv_unsigned (sp + BV 64 904)%bv = bv_unsigned sp + 904.
  { rewrite bv_add_unsigned bv_unsigned_BV.
    apply bv_wrap_small.
    pose proof (bv_unsigned_in_range 64 sp).
    unfold bv_modulus in *; cbn in *; lia. }
  have H912Address :
      bv_unsigned (sp + BV 64 912)%bv = bv_unsigned sp + 912.
  { rewrite bv_add_unsigned bv_unsigned_BV.
    apply bv_wrap_small.
    pose proof (bv_unsigned_in_range 64 sp).
    unfold bv_modulus in *; cbn in *; lia. }
  have H904Align :
      bv_extract 0 3 (sp + BV 64 904)%bv = BV 3 0.
  { clear - HspAlign.
    bv_simplify_arith HspAlign; bv_solve. }
  have H912Align :
      bv_extract 0 3 (sp + BV 64 912)%bv = BV 3 0.
  { clear - HspAlign.
    bv_simplify_arith HspAlign; bv_solve. }
  have H904RamLower :
      bv_unsigned (sp + BV 64 904)%bv >= bv_unsigned (BV 64 0x20000000) by
    apply write_success_suffix_ram_lower_904; assumption.
  have H912RamLower :
      bv_unsigned (sp + BV 64 912)%bv >= bv_unsigned (BV 64 0x20000000) by
    apply write_success_suffix_ram_lower_912; assumption.
  have H904RamUpper :
      bv_unsigned (sp + BV 64 904)%bv <=
        bv_unsigned (BV 64 0x20000000 + BV 64 0x20000000 - BV 64 8)%bv by
    apply write_success_suffix_ram_upper_904; assumption.
  have H912RamUpper :
      bv_unsigned (sp + BV 64 912)%bv <=
        bv_unsigned (BV 64 0x20000000 + BV 64 0x20000000 - BV 64 8)%bv by
    apply write_success_suffix_ram_upper_912; assumption.
  rewrite /InstrSpecs.Specs.zesu_ld_spec /InstrSpecs.Specs.rv64_ld_spec.
  iApply "Hld904".
  iExists pointer, sp.
  iAssert ("x9" ↦ᵣ: (fun _ => True))%I with "[H9]" as "H9Any".
  { rewrite reg_mapsto_pred_eq /reg_mapsto_pred_def.
    iExists _. iFrame. }
  iFrame "Hsys H9Any H2 H904".
  repeat iSplit; try iPureIntro; try assumption; try bv_solve; try lia.
  rewrite instr_pre'_eq. iNext. iIntros "Hpost".
  iDestruct "Hpost" as "(HsysPost & H9Post & H2Post & H904Post & _)".
  rewrite /InstrSpecs.Specs.zesu_ld_spec /InstrSpecs.Specs.rv64_ld_spec.
  iApply "Hld912".
  iExists (Z_to_bv 64 (Z.of_nat (S remaining))), sp.
  iAssert ("x8" ↦ᵣ: (fun _ => True))%I with "[H8]" as "H8Any".
  { rewrite reg_mapsto_pred_eq /reg_mapsto_pred_def.
    iExists _. iFrame. }
  iFrame "HsysPost H8Any H2Post H912".
  repeat iSplit; try iPureIntro; try assumption; try bv_solve; try lia.
  rewrite instr_pre'_eq. iNext. iIntros "Hpost2".
  iDestruct "Hpost2" as "(HsysPost2 & H8Post & H2Post2 & H912Post & _)".
  iPoseProof (write_success_suffix_hashes_entry_nonzero
    P sp pointer base total processed remaining bytes tail
    HremainingBound
    with "Hinstr15744 Hinstr15748 Hinstr1574c Hint Hinstr15750 Hloop")
    as "HentryBody".
  iEval (rewrite instr_pre'_eq) in "HentryBody".
  iApply "HentryBody".
  iEval (rewrite /writeSuccessSuffixHashes15744NonzeroSpec).
  iFrame.
Qed.
