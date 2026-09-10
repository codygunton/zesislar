From Coq Require Import Lists.List ZArith.ZArith.
Require Import isla.riscv64.riscv64.
From IslaTraces.write_success_blocks Require Import Index HintsTransactionsLoop.
From IslaTraces.write_success_45 Require Import a1517c_spec.
Require Import ZesuSsz.Contracts.IslarisCode.
Require Import ZesuSsz.Contracts.IslarisMachine.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessEncoderBooleanCall.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessCallAbi.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessTransactionsOptionalAddressSomeHandoff.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessTransactionsOptionalAddressSome1517cBoundary.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessTransactionsOptionalAddressSome15178Handoff.

Local Remove Hints subsume_instr_pre'_inst : typeclass_instances.
Local Existing Instance subsume_instr_pre_wand_inst | 1.

Lemma write_success_transactions_optional_address_some_1517c_core
    `{!islaG Sigma} `{!threadG} (P : iProp Sigma) :
  instr_lookup_resources IslaTraces.write_success_blocks.Index.lookup -∗
  IslaTraces.write_success_blocks.Index.spec_instr_resources -∗
  □ instr_pre 0x15b9c zesuEncoderBooleanCallSpec -∗
  instr_body 0x15180 (writeSuccessTransactionsOptionalAddressSomePostSpec P) -∗
  instr_body 0x1517c
    (writeSuccessTransactionsOptionalAddressSomeBooleanSetupSpec P).
Proof.
  move => *. iStartProof.
  iIntros "_ #Hlookup #Hcode #Hboolean Hnext".
  iPoseProof "Hlookup" as "#Hlookup1517c".
  iEval (rewrite /instr_lookup_resources) in "Hlookup1517c".
  iPoseProof ("Hlookup1517c" $! 0x1517c with "[]") as "#Hinstr1517c".
  { iPureIntro.
    rewrite IslaTraces.write_success_blocks.Index.lookup_a1517c.
    done. }
  iPoseProof (a1517c_spec 0x1517c with "Hinstr1517c") as "Hbody1517c".
  iAssert (□ (True -∗ instr_pre 0x15b9c zesuEncoderBooleanCallSpec))%I
    with "[]" as "#HbooleanHidden".
  { iModIntro. iIntros "_". iExact "Hboolean". }
  iClear "Hboolean".
  iClear "Hlookup1517c".
  iEval (rewrite instr_pre'_eq) in "Hbody1517c".
  rewrite instr_pre'_eq. iIntros "Hsetup".
  iEval (unfold writeSuccessTransactionsOptionalAddressSomeBooleanSetupSpec)
    in "Hsetup".
  iDestruct "Hsetup" as
    "(%sp & %base & %transaction & %transactions & %processed & %remaining &
      %bytes & %prefix & %suffix & %tail & Hsys & Htmp & Hcaller & Hsaved &
      H1 & H2 & H10 & H11 & Hstack & Hmmio & Htrace & Hframe & %Halign &
      %Hlower & %Hupper & _)".
  iApply "Hbody1517c".
  rewrite /InstrSpecs.Specs.zesu_jalr_same_spec.
  iExists (BV 64 0x16178). iFrame "Hsys H1".
  iSplit; first (iPureIntro; bv_solve).
  have Htarget :
    bv_unsigned
      (bv_or (bv_and ((BV 64 0x16178) + BV 64 18446744073709550116)%bv
        (BV 64 18446744073709551614)) (BV 64 0)) = 0x15b9c
    by native_compute.
  rewrite Htarget.
  iSpecialize ("HbooleanHidden" with "[]"). { done. }
  iDestruct (bi.intuitionistically_elim with "HbooleanHidden") as "HbooleanReady".
  iEval (rewrite -instr_pre'_eq) in "HbooleanReady".
  iEval (rewrite -instr_pre'_eq) in "Hnext".
  iApply (instr_pre_wand 0x15b9c 0x15b9c true true with "HbooleanReady");
    [done | reflexivity |].
  iIntros "(Hsys & H1 & _)".
  iEval (unfold zesuEncoderBooleanCallSpec, zesu_c_call).
  iExists sp, (BV 64 0x15180).
  iFrame.
  liARun.
  Unshelve.
  all: try prepare_sidecond.
  all: try assumption.
  all: try (cbn; rewrite ?length_take ?length_drop; lia).
  all: try bv_solve.
  all: try lia.
  all: try iFrame.
  Unshelve.
  iExists (b11, b10, tail, suffix, prefix, bytes, remaining, processed,
    transactions, transaction, base, sp, tt)ₗ.
  iEval (unfold writeSuccessTransactionsMachine15180).
  iEval (unfold writeSuccessTransactionsOptionalAddressSomeCallerFrame)
    in "Hframe".
  iDestruct "Hframe" as "(H34 & Hscratch & Hframe & _)".
  iRename select ((bv_unsigned sp - 16) ↦ₘ? 16)%I into "Hstack".
  iPoseProof ("Hscratch" with "Hstack") as "HscratchOut".
  iFrame.
  iRename select (reg_col ((KindReg "x1", BitsShape 64) :: _))%I
    into "Hcaller".
  iRename select (reg_col ((KindReg "x8", ExactShape _) :: _))%I
    into "Hsaved".
  iEval (rewrite !reg_col_cons reg_col_nil) in "H34 Hcaller Hsaved".
  iDestruct "H34" as "(H3 & H4 & _)".
  iDestruct "Hcaller" as
    "(H1 & H12 & H13 & H14 & H15 & H16 & H17 & H5 & H6 & H7 & H28 &
      H29 & H30 & H31 & _)".
  iDestruct "Hsaved" as
    "(H8 & H9 & H18 & H19 & H20 & H21 & H22 & H23 & H24 & H25 & H26 &
      H27 & _)".
  iDestruct "H8" as (r8) "(%Hr8 & H8)".
  iDestruct "H9" as (r9) "(%Hr9 & H9)".
  iDestruct "H18" as (r18) "(%Hr18 & H18)".
  iDestruct "H19" as (r19) "(%Hr19 & H19)".
  iDestruct "H20" as (r20) "(%Hr20 & H20)".
  iDestruct "H21" as (r21) "(%Hr21 & H21)".
  iDestruct "H22" as (r22) "(%Hr22 & H22)".
  iDestruct "H23" as (r23) "(%Hr23 & H23)".
  iDestruct "H24" as (r24) "(%Hr24 & H24)".
  iDestruct "H25" as (r25) "(%Hr25 & H25)".
  iDestruct "H26" as (r26) "(%Hr26 & H26)".
  iDestruct "H27" as (r27) "(%Hr27 & H27)".
  cbn in Hr8. cbn in Hr9. cbn in Hr18. cbn in Hr19. cbn in Hr20. cbn in Hr21.
  cbn in Hr22. cbn in Hr23. cbn in Hr24. cbn in Hr25. cbn in Hr26. cbn in Hr27.
  subst r8; subst r9; subst r18; subst r19; subst r20; subst r21.
  subst r22; subst r23; subst r24; subst r25; subst r26; subst r27.
  iEval (rewrite reg_mapsto_pred_eq /reg_mapsto_pred_def).
  cbn. iFrame.
  repeat iSplit; try iPureIntro; try done.
  iDestruct "H1" as (r1) "(%Hr1 & H1)".
  iDestruct "H5" as (r5) "(%Hr5 & H5)".
  iDestruct "H12" as (r12) "(%Hr12 & H12)".
  iSplitL "H1".
  { iExists r1. iFrame "H1". iPureIntro. exact Hr1. }
  iSplitL "H5".
  { iExists r5. iFrame "H5". iPureIntro. exact Hr5. }
  iExists r12. iFrame "H12". iPureIntro. exact Hr12.
Qed.
