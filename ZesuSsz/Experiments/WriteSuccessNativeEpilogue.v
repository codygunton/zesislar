From Coq Require Import Lists.List ZArith.ZArith Lia.
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Contracts.IslarisCode.
Require Import ZesuSsz.Contracts.IslarisMachine.
Require Import ZesuSsz.Contracts.Level1.
Require Import ZesuSsz.Experiments.WriteSuccess.
Require Import ZesuSsz.Experiments.WriteSuccessEpilogueBlock.
Require Import ZesuSsz.Experiments.WriteSuccessNativeContract.

(** This adapter converts the generic epilogue return into the exact public
    native exit.  The outer suffix can use the result as one continuation. *)
Lemma write_success_native_epilogue_continuation
    `{!islaG Sigma} `{!threadG} {State Decoded}
    (model : Level1MachineModel State Decoded)
    (outputRelation : WriteSuccessOutputRelation Decoded)
    (semantic : writeSuccessSemanticPremise model outputRelation)
    (args : WriteSuccessArgs Decoded) (witness : writeSuccessNativeWitness Decoded)
    (bytes : ByteString)
    (Hwell : writeSuccessWitnessWellFormed args witness)
    (Houtput : outputRelation args witness bytes) :
  instr_pre 0x14d10
    (∃ result : ByteString,
      ⌜writeSuccessNativeAllows model args result⌝ ∗
      writeSuccessTerminalResources outputRelation args result) -∗
  instr_pre
    (bv_unsigned
      (bv_or
        (bv_and (writeSuccessReturnValue witness + 0)%bv
          (BV 64 18446744073709551614)) (BV 64 0)))
    (writeSuccessEpiloguePost
      (writeSuccessFrameSp witness) (writeSuccessReturnValue witness)
      (writeSuccessSavedS0 witness) (writeSuccessSavedS1 witness)
      (writeSuccessSavedS2 witness) (writeSuccessSavedS3 witness)
      (writeSuccessSavedS4 witness) (writeSuccessSavedS5 witness)
      (writeSuccessSavedS6 witness) (writeSuccessSavedS7 witness)
      (writeSuccessSavedS8 witness) (writeSuccessSavedS9 witness)
      (writeSuccessSavedS10 witness) (writeSuccessSavedS11 witness) True).
Proof.
  pose proof Hwell as Hfacts.
  destruct Hfacts as
    (Hstack & HdecodedAddress & HreturnAddress & HreturnValue & Hdecoded &
     HdecodedLength & HsourceLength & HsourceBytes & HvaluesLength &
     HvaluesBytes & HpayloadLength & Hbase & Hcount & HtransactionBytes &
     HrawFacts & HwithdrawalBase & HwithdrawalCount & HwithdrawalLength &
     HwithdrawalMin & HwithdrawalMax & HspAlign & HspMin & HspMax).
  have HframeRestore :
      (writeSuccessFrameSp witness + BV 64 2000)%bv =
        writeSuccessEntrySp witness by rewrite /writeSuccessFrameSp; bv_solve.
  have HreturnBits : writeSuccessReturnValue witness = BV 64 0x14d10.
  { rewrite HreturnValue HreturnAddress. bv_solve. }
  have HreturnPc :
      bv_unsigned
        (bv_or
          (bv_and (writeSuccessReturnValue witness + 0)%bv
            (BV 64 18446744073709551614)) (BV 64 0)) = 0x14d10.
  { rewrite HreturnBits. vm_compute. reflexivity. }
  rewrite HreturnPc.
  iStartProof. iIntros "Hexit".
  iApply (instr_pre_wand 0x14d10 0x14d10 true true with "Hexit");
    [done | done |].
  iIntros "Hpost".
  iExists bytes. iSplit.
  - iPureIntro. apply writeSuccessNativeAllows_exact.
    apply semantic with witness; assumption.
  - rewrite /writeSuccessTerminalResources.
    iExists witness. iSplit; first (iPureIntro; exact Hwell).
    iSplit; first (iPureIntro; exact Houtput).
    iEval (rewrite /writeSuccessEpiloguePost /writeSuccessEpilogueFrame) in
      "Hpost".
    iDestruct "Hpost" as
      "(Hsys & H1 & Hother & H2 & H8 & H9 & H18 & H19 & H20 & H21 & H22 &
        H23 & H24 & H25 & H26 & H27 & Hslots & _ & _)".
    iEval (rewrite /writeSuccessEpilogueSavedSlots) in "Hslots".
    iDestruct "Hslots" as
      "(HslotRa & Hslot0 & Hslot1 & Hslot2 & Hslot3 & Hslot4 & Hslot5 &
        Hslot6 & Hslot7 & Hslot8 & Hslot9 & Hslot10 & Hslot11)".
    rewrite HframeRestore.
    rewrite /writeSuccessTerminalMachine /writeSuccessTerminalSavedSlots.
    iFrame.
  all: lazymatch goal with |- ?G => fail "remaining goal" G end.
Qed.
