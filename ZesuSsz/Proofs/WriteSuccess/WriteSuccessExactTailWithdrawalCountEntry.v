Require Import ZesuSsz.Automation.All.
Require Import ZesuSsz.Automation.Resources.
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Contracts.Endpoints.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessExactPrefixStackFacts.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessExactTailStackCallBounds.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessExactTailWithdrawalCountModel.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessExactTailWithdrawalCountSpec.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessExactTailWithdrawalLoadSpec.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessExactPostTransactionsWithdrawalLoad.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessNativeContract.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessRepresentation.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessValueBlock.
Require Import ZesuSsz.Proofs.WriteSuccess.Interfaces.
Open Scope Z_scope.

Lemma exact_tail_withdrawal_count_entry `{!islaG Sigma} `{!threadG}
    {Decoded} `{!WriteSuccessMemoryRepresentation Decoded}
    (args : WriteSuccessArgs Decoded) (witness : writeSuccessNativeWitness Decoded)
    (P : iProp Sigma) :
  exactTailWithdrawalLoadPost args witness P -∗
  instr_pre 0x1568c (exactTailWithdrawalCountReturn args witness P) -∗
  exactTailWithdrawalCountCallEntry args witness P.
Proof.
  iStartProof. iIntros "Hpost Hnext".
  iEval (rewrite /exactTailWithdrawalLoadPost
    /postTransactionsWithdrawalLoadPost) in "Hpost".
  iDestruct "Hpost" as
    "(Hsys & H2 & H1 & H8 & H9 & H10 & Hvalues & %Hlength & %Halign8 &
      %Hlower0 & %Hupper1896 & Hframe & _)".
  iEval (rewrite /exactTailWithdrawalLoadFrame) in "Hframe".
  iDestruct "Hframe" as
    "(Hcaller & Hsaved & Hother & H11 & Hstack & Hitems & Hmmio & Htrace &
      Hremainder & Hbase & Hown & HbaseWord & HcountWord & Hfree120 &
      Hfree1640 & Hspfree & Hcopied & Hsource & Hupper & HsavedSlots &
      Hdecoded & Hpayload & Hwithdrawals & HpostData & Hstatic & Hinvariant &
      %Hwf & HP & _)".
  iEval (rewrite /exactTailWithdrawalLoadCallerShapes; cbn) in "Hcaller".
  iDestruct "Hcaller" as
    "(H12 & H13 & H14 & H15 & H16 & H17 & H5 & H6 & H7 & H28 & H29 &
      H30 & H31 & _)".
  iEval (cbn) in "H11".
  iDestruct "H11" as "[H11 _]".
  iDestruct (mem_mapsto_uninit_split 64 with "Hstack") as
    "[Hstack64 Hstack16]"; first lia.
  have HstackAddress :
      bv_unsigned (writeSuccessFrameSp witness) - 80 + 64 =
      bv_unsigned (writeSuccessFrameSp witness) - 16 by lia.
  iEval (rewrite HstackAddress) in "Hstack16".
  have [_ [Halign16 _]] := exact_prefix_stack_facts args witness Hwf.
  have [Hlower80 HupperSp] := exact_tail_stack_call_bounds args witness Hwf.
  have Hcount := exact_tail_withdrawal_count_word args witness Hwf.
  have Hlower16 :
      mapRamBase defaultMap <= bv_unsigned (writeSuccessFrameSp witness) - 16 by
    lia.
  have Hword11 :
      default (BV 64 0) (take 69 (writeSuccessValues witness) !! 11%nat) =
      writeSuccessValueWord (writeSuccessValues witness) 11.
  { rewrite /writeSuccessValueWord lookup_take; [reflexivity | lia]. }
  have Hword12 :
      default (BV 64 0) (take 69 (writeSuccessValues witness) !! 12%nat) =
      writeSuccessValueWord (writeSuccessValues witness) 12.
  { rewrite /writeSuccessValueWord lookup_take; [reflexivity | lia]. }
  iEval (rewrite Hword11) in "H8".
  iEval (rewrite Hword12) in "H9 H10".
  iAssert (reg_col exactTailWithdrawalCountOtherCallerShapes)%I with
    "[H12 H13 H14 H15 H16 H17 H6 H7 H28 H29 H30 H31]" as "HcallerOther".
  { rewrite /exactTailWithdrawalCountOtherCallerShapes. cbn. iFrame. }
  iAssert (reg_col [(KindReg "x5", BitsShape 64);
                    (KindReg "x11", BitsShape 64)])%I
    with "[H5 H11]" as "HscratchRegs".
  { cbn. iFrame. }
  iAssert (exactTailWithdrawalCountFrame args witness P)%I with
    "[HcallerOther Hsaved Hother H8 H9 Hvalues Hstack64 Hitems Hremainder Hbase
      Hown
      HbaseWord HcountWord Hfree120 Hfree1640 Hspfree Hcopied Hsource Hupper
      HsavedSlots Hdecoded Hpayload Hwithdrawals HpostData Hstatic Hinvariant HP]"
    as "HcountFrame".
  { rewrite exactTailWithdrawalCountFrame_unfold
      /exactTailWithdrawalCommonFrame.
    iFrame. iPureIntro. exact Hwf. }
  iAssert (instr_pre (bv_unsigned (BV 64 0x1568c))
    (exactTailWithdrawalCountReturn args witness P))%I with "[Hnext]"
    as "HnextExact".
  { replace (bv_unsigned (BV 64 0x1568c)) with 0x1568c by bv_solve.
    iExact "Hnext". }
  rewrite /exactTailWithdrawalCountCallEntry.
  iFrame "Hsys HscratchRegs H1 H2 H10 Hstack16 Hmmio Htrace HcountFrame HnextExact".
  iPureIntro. repeat split; assumption.
Qed.
Print Assumptions exact_tail_withdrawal_count_entry.
