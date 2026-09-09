From Coq Require Import Lists.List ZArith.ZArith.
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Contracts.Level1.
Require Import ZesuSsz.Experiments.WriteSuccessConcreteRepresentation.
Require Import ZesuSsz.Experiments.WriteSuccessMemoryDisjoint.
Require Import ZesuSsz.Experiments.WriteSuccessNativeContract.
Require Import ZesuSsz.Experiments.WriteSuccessPrologueSpec.
Require Import ZesuSsz.Experiments.WriteSuccessStackRange.
Require Import ZesuSsz.Experiments.WriteSuccessToLoadWithFrame.
Require Import ZesuSsz.Experiments.WriteSuccessValueBlock.

Open Scope Z_scope.

Lemma writeSuccessFrameSp_unsigned {Decoded}
    (args : WriteSuccessArgs Decoded)
    (witness : writeSuccessNativeWitness Decoded) :
  writeSuccessWitnessWellFormed args witness ->
  bv_unsigned (writeSuccessFrameSp witness) =
    bv_unsigned (writeSuccessEntrySp witness) - 2000.
Proof.
  intros HwellFormed.
  have HentryLow :
      (0x20000880 <= bv_unsigned (writeSuccessEntrySp witness))%Z.
  { unfold writeSuccessWitnessWellFormed in HwellFormed. tauto. }
  unfold writeSuccessFrameSp.
  rewrite bv_sub_unsigned bv_wrap_small.
  - reflexivity.
  - have HentryRange :=
      bv_unsigned_in_range 64 (writeSuccessEntrySp witness).
    cbn in HentryRange.
    change (0 <= bv_unsigned (writeSuccessEntrySp witness) - 2000%Z <
      18446744073709551616%Z).
    change (0 <= bv_unsigned (writeSuccessEntrySp witness) <
      18446744073709551616%Z) in HentryRange.
    lia.
Qed.

Lemma writeSuccessProloguePayload_extra_data_disjoint
    `{!islaG Sigma} `{!threadG} {Decoded}
    (args : WriteSuccessArgs Decoded)
    (witness : writeSuccessNativeWitness Decoded) :
  writeSuccessWitnessWellFormed args witness ->
  writeSuccessScratch (writeSuccessEntrySp witness) -∗
  writeSuccessProloguePayload witness -∗
  ⌜writeSuccessAvoidsRange
    (writeSuccessCalleeStackLow
      (bv_unsigned (writeSuccessEntrySp witness)))
    (bv_unsigned (writeSuccessEntrySp witness))
    (bv_unsigned
      (writeSuccessValueWord (writeSuccessValues witness) 4))
    (length (writeSuccessPayload witness))⌝.
Proof.
  intros HwellFormed.
  rewrite /writeSuccessProloguePayload /writeSuccessNativeDataResources
    /writeSuccessLoadHeaderHeapResources.
  iIntros "Hscratch Hresources".
  iDestruct "Hresources" as
    "(H1896 & Hdecoded & Hmmio & Htrace & Hdata & %HdecodedLength &
      %HdecodedLow & %HdecodedHigh & _)".
  iDestruct "Hdata" as
    "(Hheap & HrawTransactions & Hwithdrawals & %HrawFacts &
      %HwithdrawalsBase & %HwithdrawalsCount & %HwithdrawalsLength &
      %HwithdrawalsLow & %HwithdrawalsHigh & Hpost)".
  iDestruct "Hheap" as
    "(H48 & H32 & Hextra & Htransactions & HtransactionsOwn &
      HtransactionsInvariant & %HsourceLength & %HvaluesBytes &
      %HvaluesLength & %HextraLength & %Hbase & %Hcount & %Halign16 &
      %Halign8 & %HframeLow & %HframeHigh & _)".
  have Hframe := writeSuccessFrameSp_unsigned args witness HwellFormed.
  iEval (rewrite Hframe) in "H48".
  iEval (rewrite Hframe) in "H32".
  iEval (replace
    (bv_unsigned (writeSuccessEntrySp witness) - 2000 - 48)%Z with
    (bv_unsigned (writeSuccessEntrySp witness) - 2048)%Z by lia) in "H48".
  iEval (replace
    (bv_unsigned (writeSuccessEntrySp witness) - 2000 - 80)%Z with
    (bv_unsigned (writeSuccessEntrySp witness) - 2080)%Z by lia) in "H32".
  iPoseProof (writeSuccessStackTiles_uninit
    (writeSuccessEntrySp witness) with "H32 H48 H1896 Hscratch") as
    "Hstack".
  have H2080 : (0 < 2080)%N by lia.
  iDestruct (mem_mapsto_uninit_disjoint
    (bv_unsigned (writeSuccessEntrySp witness) - 2080)
    (bv_unsigned (writeSuccessValueWord (writeSuccessValues witness) 4))
    2080%N (DfracOwn 1) (writeSuccessPayload witness) H2080 with
    "[$Hstack $Hextra]") as %Havoids.
  iPureIntro.
  unfold writeSuccessCalleeStackLow, writeSuccessHelperStackDepth.
  unfold writeSuccessAvoidsRange in Havoids |-.
  destruct Havoids as [Hempty | [Hbefore | Hafter]].
  - left. exact Hempty.
  - right. left. lia.
  - right. right. lia.
Qed.

Lemma writeSuccessProloguePayload_withdrawals_disjoint
    `{!islaG Sigma} `{!threadG} {Decoded}
    (args : WriteSuccessArgs Decoded)
    (witness : writeSuccessNativeWitness Decoded) :
  writeSuccessWitnessWellFormed args witness ->
  writeSuccessScratch (writeSuccessEntrySp witness) -∗
  writeSuccessProloguePayload witness -∗
  ⌜writeSuccessAvoidsRange
    (writeSuccessCalleeStackLow
      (bv_unsigned (writeSuccessEntrySp witness)))
    (bv_unsigned (writeSuccessEntrySp witness))
    (bv_unsigned (writeSuccessWithdrawalsBase witness))
    (length (writeSuccessWithdrawalsBytes witness))⌝.
Proof.
  intros HwellFormed.
  rewrite /writeSuccessProloguePayload /writeSuccessNativeDataResources
    /writeSuccessLoadHeaderHeapResources.
  iIntros "Hscratch Hresources".
  iDestruct "Hresources" as
    "(H1896 & Hdecoded & Hmmio & Htrace & Hdata & %HdecodedLength &
      %HdecodedLow & %HdecodedHigh & _)".
  iDestruct "Hdata" as
    "(Hheap & HrawTransactions & Hwithdrawals & %HrawFacts &
      %HwithdrawalsBase & %HwithdrawalsCount & %HwithdrawalsLength &
      %HwithdrawalsLow & %HwithdrawalsHigh & Hpost)".
  iDestruct "Hheap" as
    "(H48 & H32 & Hextra & Htransactions & HtransactionsOwn &
      HtransactionsInvariant & %HsourceLength & %HvaluesBytes &
      %HvaluesLength & %HextraLength & %Hbase & %Hcount & %Halign16 &
      %Halign8 & %HframeLow & %HframeHigh & _)".
  have Hframe := writeSuccessFrameSp_unsigned args witness HwellFormed.
  iEval (rewrite Hframe) in "H48".
  iEval (rewrite Hframe) in "H32".
  iEval (replace
    (bv_unsigned (writeSuccessEntrySp witness) - 2000 - 48)%Z with
    (bv_unsigned (writeSuccessEntrySp witness) - 2048)%Z by lia) in "H48".
  iEval (replace
    (bv_unsigned (writeSuccessEntrySp witness) - 2000 - 80)%Z with
    (bv_unsigned (writeSuccessEntrySp witness) - 2080)%Z by lia) in "H32".
  iPoseProof (writeSuccessStackTiles_uninit
    (writeSuccessEntrySp witness) with "H32 H48 H1896 Hscratch") as
    "Hstack".
  have H2080 : (0 < 2080)%N by lia.
  iDestruct (mem_mapsto_uninit_disjoint
    (bv_unsigned (writeSuccessEntrySp witness) - 2080)
    (bv_unsigned (writeSuccessWithdrawalsBase witness)) 2080%N
    (DfracOwn 1) (writeSuccessWithdrawalsBytes witness) H2080 with
    "[$Hstack $Hwithdrawals]") as %Havoids.
  iPureIntro.
  unfold writeSuccessCalleeStackLow, writeSuccessHelperStackDepth.
  unfold writeSuccessAvoidsRange in Havoids |-.
  destruct Havoids as [Hempty | [Hbefore | Hafter]].
  - left. exact Hempty.
  - right. left. lia.
  - right. right. lia.
Qed.


Print Assumptions writeSuccessFrameSp_unsigned.
Print Assumptions writeSuccessProloguePayload_extra_data_disjoint.
Print Assumptions writeSuccessProloguePayload_withdrawals_disjoint.
