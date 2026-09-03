From Coq Require Import Lists.List ZArith.ZArith.
Require Import isla.riscv64.riscv64.
From IslaTraces.write_success_blocks Require Import
  Index HintsTransactionsLoop.
Require Import ZesuSsz.Contracts.IslarisMachine.
Require Import ZesuSsz.Contracts.IslarisCode.
Require Import ZesuSsz.Experiments.WriteSuccessTransactionsBoundary150fc.
Require Import ZesuSsz.Experiments.WriteSuccessTransactionsBoundary15104.
Require Import ZesuSsz.Experiments.WriteSuccessTransactionsBoundary14f1c.

Import ListNotations.

Local Remove Hints subsume_instr_pre'_inst : typeclass_instances.
Local Existing Instance subsume_instr_pre_wand_inst | 1.

Lemma write_success_transactions_chunk_150fc_entry
    `{!islaG Sigma} `{!threadG} (P : iProp Sigma) :
  instr_lookup_resources IslaTraces.write_success_blocks.Index.lookup -∗
  IslaTraces.write_success_blocks.Index.spec_instr_resources -∗
  instr_body 0x15104 (writeSuccessTransactionsAt15104Spec P) -∗
  instr_body 0x150fc (writeSuccessTransactionsAt150fcSpec P).
Proof.
  move => *.
  iStartProof.
  iIntros "_ #Hlookup #Hcode Hnext".
  iEval (unfold IslaTraces.write_success_blocks.Index.spec_instr_resources)
    in "Hcode".
  liARun.
  Unshelve.
  all: try prepare_sidecond.
  all: try assumption.
  all: try bv_solve.
  all: try lia.
  all: try iFrame.
  Unshelve.
  all: repeat iIntros "?".
  all: iDestruct select (_ ∗ _)%I as
    "(Hremaining & Hmmio & Htrace & HP & Hinvariant & Hexit & _)".
  all: iPoseProof "Hinvariant" as "#HinvariantCopy".
  all: iPoseProof "HinvariantCopy" as "#HinvariantKeep".
  all: iDestruct "HinvariantCopy" as
    "(_ & _ & _ & _ & _ & _ & _ & _ & _ & %Halign & %Hmin & %Hmax & _)".
  all: have Halign8 := write_success_transactions_stack_aligned_8 sp Halign.
  all: have Hmin272 : 0x20000000 <= bv_unsigned sp + 272 by lia.
  all: have Hmax272 : bv_unsigned sp + 272 < 0x40000000 by lia.
  all: liARun.
  all: liARun.
  all: iDestruct select (reg_col
    [(KindReg "x3", BitsShape 64); (KindReg "x4", BitsShape 64);
     (KindReg "x5", BitsShape 64); (KindReg "x6", BitsShape 64);
     (KindReg "x7", BitsShape 64); (KindReg "x11", BitsShape 64);
     (KindReg "x12", BitsShape 64); (KindReg "x13", BitsShape 64);
     (KindReg "x14", BitsShape 64); (KindReg "x15", BitsShape 64);
     (KindReg "x16", BitsShape 64); (KindReg "x17", BitsShape 64);
     (KindReg "x28", BitsShape 64); (KindReg "x29", BitsShape 64);
     (KindReg "x30", BitsShape 64); (KindReg "x31", BitsShape 64)])
    as "Hregs".
  all: iEval (rewrite !reg_col_cons reg_col_nil) in "Hregs".
  all: iDestruct "Hregs" as
    "(H3 & H4 & H5 & H6 & H7 & H11 & H12 & H13 & H14 & H15 &
      H16 & H17 & H28 & H29 & H30 & H31 & _)".
  all: iDestruct "H5" as (v5 Hshape5) "H5".
  all: iDestruct "H11" as (v11 Hshape11) "H11".
  all: iAssert ("x5" ↦ᵣ: fun r5 => ⌜valu_has_shape r5 (BitsShape 64)⌝)%I
    with "[H5]" as "H5target";
    [ rewrite reg_mapsto_pred_eq /reg_mapsto_pred_def;
      iExists v5; iSplit; first iExact "H5";
      iPureIntro; exact Hshape5 | ].
  all: iAssert
    ("x11" ↦ᵣ: fun r11 => ⌜valu_has_shape r11 (BitsShape 64)⌝)%I
    with "[H11]" as "H11target";
    [ rewrite reg_mapsto_pred_eq /reg_mapsto_pred_def;
      iExists v11; iSplit; first iExact "H11";
      iPureIntro; exact Hshape11 | ].
  all: iAssert (reg_col writeSuccessTransactions15104OtherRegShapes)
    with "[H3 H4 H6 H7 H12 H13 H14 H15 H16 H17 H28 H29 H30 H31]"
    as "HtargetRegs";
    [ rewrite !reg_col_cons reg_col_nil; iFrame | ].
  all: iExists
    (tail, suffix, prefix, bytes, remaining, processed, transactions,
      transaction, base, sp, tt)ₗ.
  all: iDestruct select ("x1" ↦ᵣ RVal_Bits _)%I as "H1".
  all: iAssert ("x1" ↦ᵣ RVal_Bits (BV 64 0x16100))%I
    with "[H1]" as "H1target";
    [ replace (BV 64 0x16100) with (Z_to_bv 64 (0x15100 + 0x1000))
        by bv_solve; iExact "H1" | ].
  all: iFrame "HtargetRegs H1target H5target H11target".
  all: iFrame "Hremaining Hmmio Htrace HP HinvariantKeep Hexit".
  all: iFrame.
  all: repeat iSplit; iPureIntro; try assumption; try bv_solve; lia.
  Unshelve. all: prepare_sidecond.
  all: try assumption.
  all: try bv_solve.
  all: try lia.
Qed.
