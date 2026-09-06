From Coq Require Import Lia Lists.List ZArith.ZArith.
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Contracts.Level1.
Require Import ZesuSsz.Experiments.WriteSuccessNativeContract.
Require Import ZesuSsz.Experiments.WriteSuccessNativeCode.
Require Import ZesuSsz.Experiments.WriteSuccessNativeCalleeProviders.
Require Import ZesuSsz.Experiments.WriteSuccessLoadHeader.
Require Import ZesuSsz.Experiments.WriteSuccessPrologue.
Require Import ZesuSsz.Experiments.WriteSuccessPrologueSpec.
Require Import ZesuSsz.Experiments.WriteSuccessToLoadWithFrame.

Definition writeSuccessNativeRepresentation {Decoded}
    (represents : Decoded -> list (bv 8) -> Prop)
    (args : WriteSuccessArgs Decoded)
    (witness : writeSuccessNativeWitness Decoded) : Prop :=
  represents (successDecoded Decoded args) (writeSuccessDecodedBytes witness).

Definition writeSuccessRepresentedNativeEntry `{!islaG Sigma} `{!threadG}
    {Decoded} (represents : Decoded -> list (bv 8) -> Prop)
    (args : WriteSuccessArgs Decoded) : iProp Sigma :=
  (∃ witness : writeSuccessNativeWitness Decoded,
    ⌜writeSuccessWitnessWellFormed args witness⌝ ∗
    ⌜writeSuccessNativeRepresentation represents args witness⌝ ∗
    write_success_prologue_entry
      (writeSuccessEntrySp witness) (writeSuccessDecodedPointer witness)
      (writeSuccessReturnValue witness)
      (writeSuccessSavedS0 witness) (writeSuccessSavedS1 witness)
      (writeSuccessSavedS2 witness) (writeSuccessSavedS3 witness)
      (writeSuccessSavedS4 witness) (writeSuccessSavedS5 witness)
      (writeSuccessSavedS6 witness) (writeSuccessSavedS7 witness)
      (writeSuccessSavedS8 witness) (writeSuccessSavedS9 witness)
      (writeSuccessSavedS10 witness) (writeSuccessSavedS11 witness)
      (writeSuccessProloguePayload witness))%I.

Global Instance : LithiumUnfold (@writeSuccessRepresentedNativeEntry) := I.

Definition writeSuccessRepresentedLoadResources {Decoded}
    (represents : Decoded -> list (bv 8) -> Prop)
    `{!islaG Sigma} `{!threadG} :
    IslarisContractResources (WriteSuccessArgs Decoded)
      (writeSuccessNativeWitness Decoded) := {|
  islarisCode := writeSuccessCompleteNativeCode;
  islarisEntry := writeSuccessRepresentedNativeEntry represents;
  islarisExit := fun _ witness =>
    writeSuccessAtLoadHeaderWithFrame
      (writeSuccessFrameSp witness)
      (take 720 (writeSuccessDecodedBytes witness))
      (writeSuccessNativeTailEvents witness)
      (reg_col writeSuccessLoadHeaderExtraRegisters ∗
       writeSuccessNativeDataResources witness)
|}.

Definition writeSuccessRepresentedLoadAllows {Decoded}
    (represents : Decoded -> list (bv 8) -> Prop)
    (args : WriteSuccessArgs Decoded)
    (witness : writeSuccessNativeWitness Decoded) : Prop :=
  writeSuccessWitnessWellFormed args witness /\
  writeSuccessNativeRepresentation represents args witness.

Theorem write_success_represented_prefix_correct {Decoded}
    (represents : Decoded -> list (bv 8) -> Prop)
    `{!islaG Sigma} `{!threadG} :
  ⊢ IslarisContractSpec 0x14d30 0x14d80
    (writeSuccessRepresentedLoadAllows represents)
    (@writeSuccessRepresentedLoadResources Decoded represents Sigma _ _).
Proof.
  rewrite /IslarisContractSpec /writeSuccessRepresentedLoadResources /=.
  iStartProof.
  iIntros "#Hnative" (args).
  rewrite instr_pre'_eq. iIntros "Hcontract".
  iDestruct "Hcontract" as "[Hentry Hexit]".
  iEval (rewrite /writeSuccessRepresentedNativeEntry) in "Hentry".
  iDestruct "Hentry" as (witness) "(%HwellFormed & %Hrepresents & Hentry)".
  pose proof HwellFormed as HwellFormedCopy.
  destruct HwellFormed as
    (Hstack & HdecodedAddress & HreturnAddress & HreturnValue &
     Hdecoded & HdecodedLength & HsourceLength & HsourceBytes &
     HvaluesLength & HvaluesBytes & HpayloadLength & Hbase & Hcount &
     HtransactionBytes & HrawFacts & HwithdrawalBase & HwithdrawalCount &
     HwithdrawalLength & HwithdrawalMin & HwithdrawalMax & HspAlign & HspMin &
     HspMax).
  have HdecodedMin :
      (0x20000000 <= bv_unsigned (writeSuccessDecodedPointer witness))%Z
    by lia.
  have HdecodedMax :
      (bv_unsigned (writeSuccessDecodedPointer witness) + 848 <
       0x40000000)%Z by lia.
  have HspExtract :
      bv_extract 0 4 (writeSuccessEntrySp witness) = BV 4 0.
  { apply bv_eq. rewrite bv_extract_0_unsigned.
    unfold bv_wrap, bv_modulus. cbn. exact HspAlign. }
  iPoseProof (write_success_native_callee_providers with
    "Hnative") as "#Hcallees".
  iEval (rewrite /writeSuccessNativeCalleeProviders) in "Hcallees".
  iDestruct "Hcallees" as
    "(#Houtput & #Hmemcpy & #Hboolean & #Hoptional & #HbyteLists &
      #Hbytes & #Hu256 & #Hint1645 & #Hint & _)".
  iEval (rewrite /writeSuccessCompleteNativeCode) in "Hnative".
  iDestruct "Hnative" as
    "(#Hprologue & #Hlookup & #Hmain & #HoutputCode & #HmemcpyCode &
      #HbooleanCode & #HoptionalCode & #HbyteListsCode & #HbytesCode &
      #HintCode & #Hu256Code & #Hint1645Code)".
  iEval (rewrite -instr_pre'_eq) in "Hexit".
  iAssert (instr_pre 0x14d80
      (writeSuccessAtLoadHeaderWithFrame
        (writeSuccessFrameSp witness)
        (take 720 (writeSuccessDecodedBytes witness))
        (writeSuccessNativeTailEvents witness)
        (reg_col writeSuccessLoadHeaderExtraRegisters ∗
         writeSuccessNativeDataResources witness)))%I
    with "[Hexit]" as "Hload".
  { iApply (instr_pre_wand with "Hexit"); [done | done |].
    iIntros "Hload".
    iExists witness. iSplit.
    - iPureIntro. split; assumption.
    - iExact "Hload". }
  iPoseProof (write_success_prologue
    (writeSuccessEntrySp witness) (writeSuccessDecodedPointer witness)
    (writeSuccessReturnValue witness)
    (writeSuccessSavedS0 witness) (writeSuccessSavedS1 witness)
    (writeSuccessSavedS2 witness) (writeSuccessSavedS3 witness)
    (writeSuccessSavedS4 witness) (writeSuccessSavedS5 witness)
    (writeSuccessSavedS6 witness) (writeSuccessSavedS7 witness)
    (writeSuccessSavedS8 witness) (writeSuccessSavedS9 witness)
    (writeSuccessSavedS10 witness) (writeSuccessSavedS11 witness)
    (writeSuccessProloguePayload witness) with "Hprologue") as "Hbody".
  iEval (rewrite instr_pre'_eq) in "Hbody".
  iApply "Hbody".
  iSplitL "Hentry"; first iExact "Hentry".
  iSplit; last done.
  iNext. iIntros "Hhandoff".
  iPoseProof (write_success_to_load_with_frame_extra
    (writeSuccessEntrySp witness) (writeSuccessDecodedPointer witness)
    (writeSuccessReturnValue witness)
    (writeSuccessSavedS0 witness) (writeSuccessSavedS1 witness)
    (writeSuccessSavedS2 witness) (writeSuccessSavedS3 witness)
    (writeSuccessSavedS4 witness) (writeSuccessSavedS5 witness)
    (writeSuccessSavedS6 witness) (writeSuccessSavedS7 witness)
    (writeSuccessSavedS8 witness) (writeSuccessSavedS9 witness)
    (writeSuccessSavedS10 witness) (writeSuccessSavedS11 witness)
    (writeSuccessDecodedBytes witness) (writeSuccessNativeAfterTagEvents witness)
    (writeSuccessNativeDataResources witness)
    Hdecoded HspExtract HspMin HspMax with
    "Hlookup Hmain HmemcpyCode HoutputCode Hmemcpy Houtput Hload") as "HtoLoad".
  iEval (rewrite instr_pre'_eq) in "HtoLoad".
  iApply "HtoLoad". iExact "Hhandoff".
Qed.

Print Assumptions write_success_represented_prefix_correct.
