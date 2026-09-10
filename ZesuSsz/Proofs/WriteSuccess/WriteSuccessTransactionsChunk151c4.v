Require Import ZesuSsz.Automation.All.
From Coq Require Import Lists.List ZArith.ZArith.
Require Import isla.riscv64.riscv64.
From IslaTraces.write_success_blocks Require Import
  Index HintsTransactionsLoop.
Require Import ZesuSsz.Contracts.IslarisMachine.
Require Import ZesuSsz.Contracts.IslarisCode.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessEncoderIntCall.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessTransactionsBoundary151c4.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessTransactionsBoundary151d0.

Local Remove Hints subsume_instr_pre'_inst : typeclass_instances.
Local Existing Instance subsume_instr_pre_wand_inst | 1.

Lemma write_success_transactions_chunk_151c4
    `{!islaG Sigma} `{!threadG} (P : iProp Sigma) :
  instr_lookup_resources IslaTraces.write_success_blocks.Index.lookup -∗
  IslaTraces.write_success_blocks.Index.spec_instr_resources -∗
  □ instr_pre 0x15d10 zesuEncoderIntCallSpec -∗
  instr_body 0x151d0 (writeSuccessTransactionsAt151d0Spec P) -∗
  instr_body 0x151c4 (writeSuccessTransactionsAt151c4Spec P).
Proof.
  move => *.
  iStartProof.
  iIntros "_ #Hlookup #Hcode #Hint Hnext".
  iEval (unfold IslaTraces.write_success_blocks.Index.spec_instr_resources)
    in "Hcode".
  liARun.
  Unshelve.
  all: try prepare_sidecond.
  all: try assumption.
  all: try (cbn; rewrite ?length_take ?length_drop; lia).
  all: try bv_solve.
  all: try lia.
  all: try iFrame.
  Unshelve.
  all: repeat iIntros "?".
  all: iDestruct select (base ↦ₘ∗ prefix ∗ _)%I as
    "(HbasePrefix & HbaseSuffix & Hprocessed & Htransaction & Hremaining &
      Hmmio & Htrace & HP & #Hinvariant & Hexit & _)".
  all: iPoseProof "Hinvariant" as "#HinvariantCopy".
  all: iDestruct "HinvariantCopy" as
    "(_ & _ & _ & _ & _ & _ & _ & _ & _ & %Halign & %Hmin & %Hmax & _)".
  all: have Halign8 : (bv_unsigned sp mod 8 = 0)%Z.
  { apply Z.mod_divide in Halign; [|lia].
    destruct Halign as [k Hk].
    apply Z.mod_divide; [lia|].
    exists (2 * k)%Z. lia. }
  all: have Hmin264 : (0x20000000 <= bv_unsigned sp + 264)%Z by lia.
  all: have Hmax264 : (bv_unsigned sp + 264 < 0x40000000)%Z by lia.
  all: liARun.
  all: iSplit; [|done].
  all: iIntros "Hpost".
  all: iDestruct "Hpost" as
    "(Hsys & H1 & H2 & H5 & H10 & H11 & Hstack & Hmmio & Htrace & _)".
  all: iDestruct select ((bv_unsigned sp - 48) ↦ₘ? 32)%I as "Hlower".
  all: iDestruct select ((bv_unsigned sp - 16 + 16) ↦ₘ? 104)%I
    as "Hupper".
  all: have HupperAddress : bv_unsigned sp - 16 + 16 = bv_unsigned sp by lia.
  all: iEval (rewrite HupperAddress) in "Hupper".
  all: iAssert ((bv_unsigned sp - 48) ↦ₘ? 48)%I
    with "[Hlower Hstack]" as "Hlower48".
  { iApply (mem_mapsto_uninit_combine 32 with "Hlower"); first lia.
    have -> : bv_unsigned sp - 48 + 32 = bv_unsigned sp - 16 by lia.
    iExact "Hstack". }
  all: iAssert ((bv_unsigned sp - 48) ↦ₘ? 152)%I
    with "[Hlower48 Hupper]" as "HscratchPrefix".
  { iApply (mem_mapsto_uninit_combine 48 with "Hlower48"); first lia.
    have -> : bv_unsigned sp - 48 + 48 = bv_unsigned sp by lia.
    iExact "Hupper". }
  all: iAssert ("x1" ↦ᵣ RVal_Bits (BV 64 0x151d0))%I
    with "[H1]" as "H1target".
  { replace (BV 64 0x151d0) with (Z_to_bv 64 (0x151cc + 4)) by bv_solve.
    iExact "H1". }
  all: iExists sp, base, transaction, transactions, processed, remaining,
    bytes, prefix, suffix, tail.
  all: iFrame "Hsys H1target H2 H5 H10 H11 HscratchPrefix HbasePrefix
    HbaseSuffix Hprocessed Htransaction Hremaining Hmmio Htrace HP Hinvariant
    Hexit".
  all: iFrame.
  all: repeat iSplit; iPureIntro; try assumption; try bv_solve; lia.
  Unshelve. all: prepare_sidecond.
  all: try bv_solve.
  all: try lia.
  Unshelve.
  all: try exact Halign8.
  all: try exact Hmin264.
  all: try exact Hmax264.
  all: try lia.
Qed.
