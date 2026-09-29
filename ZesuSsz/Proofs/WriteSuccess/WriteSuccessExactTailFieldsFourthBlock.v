Require Import ZesuSsz.Automation.All.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessExactTailFieldsSourceJunction.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessExactTailFieldsCallerJunction.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessExactTailFieldsTraceJunction.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessExactTailFieldsPayloadJunction.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessExactSuffixBytesPayloadSpec.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessExactSuffixBytesPayload158e0.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessNativeContract.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessRepresentation.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessExactEncoderBytes.
Require Import ZesuSsz.Proofs.WriteSuccess.Interfaces.
Require Import ZesuSsz.Contracts.IslarisCode.
Require Import ZesuSsz.Contracts.IslarisMemory.
Require Import ZesuSsz.Automation.ArrayLoadPriority.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessPostTransactionDescriptors.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessPostTransactionResources.
Require Import ZesuSsz.Contracts.Endpoints.
Require Import isla.riscv64.riscv64.
From IslaTraces.write_success_blocks Require Import Index.
Open Scope Z_scope.

Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessExactTailFieldsFirstResources.
Lemma write_success_exact_tail_fields_fourth_block
    `{!islaG Sigma} `{!threadG}
    {Decoded} `{!WriteSuccessMemoryRepresentation Decoded}
    (args : WriteSuccessArgs Decoded) (witness : writeSuccessNativeWitness Decoded)
    (oldS1 : bv 64) :
  instr_lookup_resources IslaTraces.write_success_blocks.Index.lookup -∗
  IslaTraces.write_success_blocks.Index.spec_instr_resources -∗
  □ instr_pre 0x15c6c encoderBytesEntryBoundary -∗
  □ instr_pre 0x15c10 encoderByteListsEntryBoundary -∗
  □ instr_pre 0x15d10 encoderIntEntryBoundary -∗
  instr_body 0x15920
    (tailFieldsCallerReturn args witness oldS1 (BV 64 0x15920)
      (writeSuccessPostBytes15910 (writeSuccessPostData witness))
      (tailFieldsAfterFourthCallEvents witness)) -∗
  instr_body 0x15910
    (tailFieldsCallerReturn args witness oldS1 (BV 64 0x15910)
      (writeSuccessPostBytes15900 (writeSuccessPostData witness))
      (tailFieldsAfterThirdCallEvents witness)).
Proof.
  zesu_block.
  all: have Hscratch : (writeSuccessEntrySp witness - (BV 64 2000 + BV 64 48))%bv = (writeSuccessFrameSp witness - BV 64 48)%bv by (unfold writeSuccessFrameSp; bv_solve).
  all: have HheaderAddress : bv_unsigned (writeSuccessFrameSp witness) - 48 = bv_unsigned (writeSuccessEntrySp witness - (BV 64 2000 + BV 64 48))%bv by (rewrite Hscratch; bv_solve).
  all: rewrite -HheaderAddress Z.sub_diag /=; try lia.
  iRename select (instr_body 0x15920 _) into "Hnext".
  repeat ZesuSsz.Automation.ArrayLoadPriority.zesu_normalize_word_array_lookup.
  iRename select (tailFieldsActivePayloads _ _) into "Hactive".
  iEval (rewrite tailFieldsActivePayloads_unfold) in "Hactive".
  iDestruct "Hactive" as "(Hsecond & Hthird & Hfourth & Hfifth & Hlist1 & Hlist2 & Hlist3 & _)".
  iEval (unfold writeSuccessDescriptorResources) in "Hfourth".
  iDestruct "Hfourth" as "[Hpayload %Hlength]".
  iRename select (spec_trace _) into "Htrace".
  iEval (unfold tailFieldsAfterThirdCallEvents, tailFieldsBytesCallEvents) in "Htrace".
  iExists (tailFieldsAfterFourthCallEvents witness, BV 64 0x15910, BV 64 0, oldS1,
    stack2, BV 64 0x15c90, writeSuccessPostBytes15910Payload (writeSuccessPostData witness), tt)ₗ.
  iFrame. iIntros "Hprefix Hsuffix". rewrite Hscratch. iFrame.
  repeat iSplit; try (iPureIntro; first [assumption | bv_solve | lia]).
  all: try done.
  all: try (iPureIntro; let alignedPointer := fresh "alignedPointer" in
    remember (writeSuccessFrameSp witness) as alignedPointer in *; clear -H1; bv_solve).
  replace (bv_unsigned (Z_to_bv 64 88348 + 4)%bv) with 0x15920 by bv_solve.
  iApply instr_pre_to_body. iNext.
  iEval (rewrite instr_pre'_eq). iIntros "Hpost".
  iEval (unfold encoderBytesExactReturn, encoderBytesExactPost, encoderBytesExactOutputResources) in "Hpost".
  repeat iDestruct select (_ ∗ _)%I as "[? ?]".
  have Hret : (Z_to_bv 64 88348 + 4)%bv = BV 64 0x15920 by bv_solve. rewrite Hret.
  iEval (rewrite instr_pre'_eq) in "Hnext".
  iApply ("Hnext" with "[-]").
  iEval (unfold tailFieldsCallerReturn). iExists stack2.
  iEval (rewrite /tailFieldsCallerPrepared tailFieldsActivePayloads_unfold /writeSuccessDescriptorResources /encoderBytesExactOutputResources).
  iDestruct select (reg_col ((KindReg "x3", BitsShape 64) :: _))%I as "Hother"; iEval (rewrite /reg_col /=) in "Hother"; repeat iDestruct select (_ ∗ _)%I as "[? ?]".
  iFrame. repeat iSplit; try (iPureIntro; first [assumption | lia]); done.
Qed.
Print Assumptions write_success_exact_tail_fields_fourth_block.
