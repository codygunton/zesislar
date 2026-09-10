From Coq Require Import Lists.List ZArith.ZArith.
Require Import isla.riscv64.riscv64.
From IslaTraces.write_success_blocks Require Import Index.
Require Import ZesuSsz.Contracts.IslarisMachine.
Require Import ZesuSsz.Contracts.IslarisCode.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessLoopCommon.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessSuffixHashesEntryCallerResources.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessSuffixHashes15740Raw.
Require Import InstrSpecs.Lookup.

Local Remove Hints subsume_instr_pre'_inst : typeclass_instances.
Local Existing Instance subsume_instr_pre_wand_inst | 1.

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
  iPoseProof (write_success_suffix_hashes_a15740_raw
    with "Hinstr15740") as "Hld912".
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
