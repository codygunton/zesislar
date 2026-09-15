Require Import ZesuSsz.Automation.All.
Require Import ZesuSsz.Automation.Resources.
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Contracts.Endpoints.
Require Import ZesuSsz.Contracts.IslarisMemory.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessNativeContract.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessRepresentation.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessValueBlock.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessByteLists.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessTransactionsSpec.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessExactTransactionsLiveSpec.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessPostTransactionResources.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessPostTransactionDescriptors.
Require Import ZesuSsz.Proofs.WriteSuccess.Interfaces.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessExactValueSpec.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessExactPostTransactionsWithdrawalLoad.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessExactSuffixByteListPayloadAtSpec.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessExactTailRawCallSpec.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessExactTailRawCallReturnSpec.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessExactTailWithdrawalLoadSpec.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessExactPrefixStackFacts.
Open Scope Z_scope.

Lemma exact_tail_raw_return_to_withdrawal_load `{!islaG Sigma} `{!threadG}
    {Decoded} `{!WriteSuccessMemoryRepresentation Decoded}
    (args : WriteSuccessArgs Decoded) (witness : writeSuccessNativeWitness Decoded)
    (P : iProp Sigma) :
  exactTailRawCallReturn args witness P -∗
  exactTailWithdrawalLoadEntry args witness P.
Proof.
  iStartProof. iIntros "Hreturn".
  iEval (rewrite /exactTailRawCallReturn /exactSuffixByteListReturnAt
    /zesu_c_call_ret /exactTailRawCallFrame /exactTailRawCallMemoryFrame
    /writeSuccessExactValueMemory) in "Hreturn".
  iDestruct "Hreturn" as
    (s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11) "Hreturn".
  iDestruct "Hreturn" as "[Hcallret Hframe]".
  iDestruct "Hframe" as "[Hother Hmemory]".
  iDestruct "Hcallret" as "(Hsys & Hcaller & Hsaved & Hbits)".
  iEval (rewrite reg_mapsto_pred_eq /reg_mapsto_pred_def) in "Hbits".
  iDestruct "Hbits" as (r10) "[H10 Hbits]".
  iDestruct "Hbits" as (b10) "[%Hr10 Hbits]". subst r10.
  iDestruct "Hbits" as (r11) "[H11 Hbits]".
  iDestruct "Hbits" as (b11) "[%Hr11 Hbits]". subst r11.
  iDestruct "Hbits" as "(H2 & Hstack & Hcall)".
  iDestruct "Hcall" as "(Hitems & Hmmio & Htrace & _)".
  iDestruct "Hmemory" as
    "(Hbase & Hown & HbaseWord & HcountWord & Hfree120 & Hfree1640 & Hspfree &
      Hcopied & Hsource & Hvalues & Hupper & HsavedSlots & Hdecoded & Hpayload &
      Hwithdrawals & Hpost & Hstatic & Hinvariant & Hwf & HP & _)".
  iDestruct "Hvalues" as "(Hvalues69 & Hvalues4 & Hhash & HvaluesTail)".
  iDestruct "Hwf" as %Hwf.
  have HvaluesLength : length (writeSuccessValues witness) = 74%nat.
  { unfold writeSuccessWitnessWellFormed in Hwf. tauto. }
  have HtakeLength : length (take 69 (writeSuccessValues witness)) = 69%nat.
  { rewrite length_take HvaluesLength. lia. }
  have [Hframe [Halign Hupper]] := exact_prefix_stack_facts args witness Hwf.
  have Hlower : 0 <= bv_unsigned (writeSuccessFrameSp witness).
  { pose proof (bv_unsigned_in_range 64 (writeSuccessFrameSp witness)). lia. }
  iEval (unfold tmp_registers; cbn) in "Hcaller".
  iDestruct "Hcaller" as "[H1 Hcaller]".
  iDestruct "H1" as (r1) "[%Hr1 H1]".
  apply valu_has_bits_shape in Hr1. destruct Hr1 as (oldra & ->).
  iEval (cbn) in "Hsaved".
  iDestruct "Hsaved" as
    "(H8 & H9 & H18 & H19 & H20 & H21 & H22 & H23 & H24 & H25 & H26 & H27 & _)".
  iDestruct "H8" as (r8) "[%Hr8 H8]". simpl in Hr8. subst r8.
  iDestruct "H9" as (r9) "[%Hr9 H9]". simpl in Hr9. subst r9.
  iAssert (reg_col (zip_with (fun register value =>
      (KindReg register, ExactShape value))
    ["x18"; "x19"; "x20"; "x21"; "x22"; "x23"; "x24"; "x25"; "x26"; "x27"]
    ((fun value : bv 64 => RVal_Bits value) <$>
      [s2; s3; s4; s5; s6; s7; s8; s9; s10; s11])))%I with
    "[H18 H19 H20 H21 H22 H23 H24 H25 H26 H27]" as "HsavedExact".
  { cbn. iFrame. }
  iPoseProof (reg_col_exact_bv_to_bits
    ["x18"; "x19"; "x20"; "x21"; "x22"; "x23"; "x24"; "x25"; "x26"; "x27"]
    [s2; s3; s4; s5; s6; s7; s8; s9; s10; s11]
    ltac:(reflexivity) with "HsavedExact") as "HsavedBits".
  iAssert (reg_col exactTailWithdrawalLoadCallerShapes)%I with "[Hcaller]"
    as "HcallerFrame".
  { rewrite /exactTailWithdrawalLoadCallerShapes. iExact "Hcaller". }
  iAssert (reg_col [(KindReg "x11", BitsShape 64)])%I with "[H11]" as "H11Bits".
  { rewrite reg_col_cons reg_col_nil. iSplitL "H11"; last done.
    iExists (RVal_Bits b11). iFrame. done. }
  iAssert (exactTailWithdrawalLoadFrame args witness P)%I with
    "[HcallerFrame HsavedBits Hother H11Bits Hstack Hitems Hmmio Htrace Hvalues4
      Hhash HvaluesTail Hbase Hown HbaseWord HcountWord Hfree120 Hfree1640
      Hspfree Hcopied Hsource Hupper HsavedSlots Hdecoded Hpayload Hwithdrawals
      Hpost Hstatic Hinvariant HP]" as "HloadFrame".
  { rewrite /exactTailWithdrawalLoadFrame /exactTailWithdrawalValueRemainder
      /exactTailWithdrawalLoadCallerShapes /exactTailWithdrawalLoadSavedShapes.
    iFrame. iPureIntro. exact Hwf. }
  rewrite /exactTailWithdrawalLoadEntry /postTransactionsWithdrawalLoadEntry.
  iExists oldra, s0, s1, b10.
  iFrame "Hsys H2 H1 H8 H9 H10 Hvalues69 HloadFrame".
  repeat iSplit; iPureIntro; try assumption; lia.
Qed.

Print Assumptions exact_tail_raw_return_to_withdrawal_load.
