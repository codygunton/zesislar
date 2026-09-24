Require Import ZesuSsz.Automation.All.
Require Import ZesuMachineMap.Machine.
From Coq Require Import Lists.List ZArith.ZArith.
Require Import isla.riscv64.riscv64.
From IslaTraces.write_success_blocks Require Import Index.
Require Import ZesuSsz.Contracts.Endpoints.
Require Import ZesuSsz.Proofs.WriteSuccess.Interfaces.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessNativeContract.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessOutputSemantic.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessPostTransactionDescriptors.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessExactPrefixStackFacts.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessRepresentation.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessValueSpec.

Definition writeSuccessExactPost1573cEvents {Decoded}
    (witness : writeSuccessNativeWitness Decoded) : spec :=
  let descriptors := writeSuccessPost1573cDescriptors
    (writeSuccessFrameSp witness) (writeSuccessPostData witness) in
  writeOutputPayloadsSpec descriptors
    (writeSuccessExactPostPayloadsAt descriptors witness)
    (writeSuccessTraceTail witness).

Definition writeSuccessExactPostWithdrawalsTailAt {Decoded}
    (offset : nat) (witness : writeSuccessNativeWitness Decoded) : spec :=
  writeOutputPayloadsSpec
    (drop offset (writeSuccessPost156e8Descriptors
      (writeSuccessFrameSp witness) (writeSuccessPostData witness)))
    (drop offset (writeSuccessExactPostWithdrawalsPayloads witness))
    (writeSuccessTraceTail witness).

Definition writeSuccessExactPostWithdrawalsAfterOptionalIndex {Decoded}
    (witness : writeSuccessNativeWitness Decoded) : nat :=
  2 + length (WriteSuccessOutputDescriptors.writeSuccessOptionalU64Descriptors
    (writeSuccessFrameSp witness)
    (writeSuccessPostOptional15700 (writeSuccessPostData witness))).

Definition writeSuccessExactPostWithdrawalsAfterBytesIndex {Decoded}
    (witness : writeSuccessNativeWitness Decoded) : nat :=
  writeSuccessExactPostWithdrawalsAfterOptionalIndex witness +
  length (WriteSuccessOutputDescriptors.writeSuccessBytesDescriptors (writeSuccessFrameSp witness)
    (fst (writeSuccessPostBytes1571c (writeSuccessPostData witness)))
    (snd (writeSuccessPostBytes1571c (writeSuccessPostData witness)))).

Lemma exact_post_withdrawals_second_tail_explicit {Decoded}
    (witness : writeSuccessNativeWitness Decoded) :
  exactPostWithdrawalsFirstTail witness =
    Snapshots.writeOutputEvents (writeSuccessFrameSp witness - BV 64 16)%bv
      (BV 64 8)
      (writeSuccessPrivateBytes (WriteSuccessObservation.writeSuccessEncodeU64
        (bv_unsigned (writeSuccessValueWord (writeSuccessValues witness) 14))))
      (writeSuccessExactPostWithdrawalsTailAt 2 witness).
Proof.
  rewrite /exactPostWithdrawalsFirstTail
    /writeSuccessExactPostWithdrawalsTailAt /writeSuccessPost156e8Descriptors
    exact_post_withdrawals_payloads.
  cbn [WriteSuccessExactTrace.writeSuccessPostFragments
    WriteSuccessExactTrace.writeSuccessExactObservation
    WriteSuccessRepresentation.writeSuccessNativeObservation
    writeOutputPayloadsSpec].
  reflexivity.
Qed.

Lemma exact_post_withdrawals_second_event {Decoded}
    (witness : writeSuccessNativeWitness Decoded) :
  Snapshots.writeOutputEvents (writeSuccessFrameSp witness - BV 64 16)%bv
      (BV 64 8)
      (writeSuccessPrivateBytes (WriteSuccessObservation.writeSuccessEncodeU64
        (bv_unsigned (writeSuccessValueWord (writeSuccessValues witness) 14))))
      (writeSuccessExactPostWithdrawalsTailAt 2 witness)
    ⊆ exactPostWithdrawalsFirstTail witness.
Proof.
  rewrite exact_post_withdrawals_second_tail_explicit. reflexivity.
Qed.

Definition exactPostWithdrawalsSecondContinuation {Decoded}
    (witness : writeSuccessNativeWitness Decoded) : spec :=
  scons_snap
    (SWriteMem (BV 64 (machineOutputSizeAddress defaultMap)) (BV 64 8))
    (fun snapshot =>
      read_mem_list snapshot.(snap_mem)
        (bv_unsigned (writeSuccessFrameSp witness - BV 64 16)) 8 =
      Some (writeSuccessPrivateBytes
        (WriteSuccessObservation.writeSuccessEncodeU64
          (bv_unsigned
            (writeSuccessValueWord (writeSuccessValues witness) 14)))))
    (writeSuccessExactPostWithdrawalsTailAt 2 witness).

Lemma exact_post_withdrawals_second_continuation {Decoded}
    (witness : writeSuccessNativeWitness Decoded) :
  exactPostWithdrawalsFirstTail witness =
    scons
      (SWriteMem (BV 64 (machineOutputAddress defaultMap))
        (writeSuccessFrameSp witness - BV 64 16)%bv)
      (exactPostWithdrawalsSecondContinuation witness).
Proof.
  rewrite exact_post_withdrawals_second_tail_explicit.
  reflexivity.
Qed.

Definition writeSuccessExactPostWithdrawalsExitFrame
    `{!islaG Sigma} `{!threadG} {Decoded}
    `{!WriteSuccessMemoryRepresentation Decoded}
    (args : WriteSuccessArgs Decoded)
    (witness : writeSuccessNativeWitness Decoded)
    (P : iProp Sigma) : iProp Sigma :=
  let sp := writeSuccessFrameSp witness in
  (reg_col ((fun register => (KindReg register, BitsShape 64)) <$>
      ["x1"; "x5"; "x9"; "x11"; "x12"; "x13"; "x14"; "x15"; "x18"]) ∗
   "x2" ↦ᵣ RVal_Bits sp ∗
   bv_unsigned (writeSuccessWithdrawalsBase witness) ↦ₘ∗
     writeSuccessWithdrawalsBytes witness ∗
   (bv_unsigned sp + 1744) ↦ₘ? 48 ∗
   (bv_unsigned sp - 16) ↦ₘ? 16 ∗
   mmio_range (machineOutputAddress defaultMap) 16 ∗
   spec_trace (writeSuccessExactPost1573cEvents witness) ∗
   writeSuccessExactPostWithdrawalsCallerFrame args witness ∗ P ∗ True)%I.

Global Instance : LithiumUnfold
  (@writeSuccessExactPostWithdrawalsExitFrame) := I.

Lemma post_withdrawals_stack_facts {Decoded}
    `{!WriteSuccessMemoryRepresentation Decoded}
    (args : WriteSuccessArgs Decoded) (witness : writeSuccessNativeWitness Decoded) :
  writeSuccessWitnessWellFormed args witness ->
  bv_extract 0 3 (writeSuccessFrameSp witness + BV 64 1136) = BV 3 0 /\
  bv_unsigned (writeSuccessFrameSp witness + BV 64 1136) <=
    bv_unsigned (BV 64 (machineRamEnd defaultMap) - BV 64 8) /\
  bv_unsigned (writeSuccessFrameSp witness + BV 64 1136) =
    bv_unsigned (writeSuccessFrameSp witness) + 1136.
Proof.
  intros Hwf. have [_ [Halign Hupper]] := exact_prefix_stack_facts args witness Hwf.
  have Hdelta := zesu_bv_unsigned_add_Z_64 (writeSuccessFrameSp witness) 1136
    ltac:(cbv [machineRamEnd mapRamSize mapRamBase defaultMap] in Hupper; lia).
  have Haddress : bv_unsigned (writeSuccessFrameSp witness + BV 64 1136) = bv_unsigned (writeSuccessFrameSp witness) + 1136 by
    (change (bv_unsigned (writeSuccessFrameSp witness + Z_to_bv 64 1136) = bv_unsigned (writeSuccessFrameSp witness) + 1136); lia).
  split; [bv_solve|]. split.
  - change (bv_unsigned (writeSuccessFrameSp witness + BV 64 1136) <= 1073741816).
    rewrite Haddress. lia.
  - exact Haddress.
Qed.

Lemma write_success_exact_post_withdrawals_segment
    `{!islaG Sigma} `{!threadG} {Decoded}
    `{!WriteSuccessMemoryRepresentation Decoded}
    (args : WriteSuccessArgs Decoded)
    (witness : writeSuccessNativeWitness Decoded) (P : iProp Sigma)
    (Hwf : writeSuccessWitnessWellFormed args witness) :
  instr_lookup_resources IslaTraces.write_success_blocks.Index.lookup -∗
  IslaTraces.write_success_blocks.Index.spec_instr_resources -∗
  □ instr_pre 0x15d10 encoderIntEntryBoundary -∗
  □ instr_pre 0x15bc8 encoderOptionalEntryBoundary -∗
  □ instr_pre 0x15c6c encoderBytesEntryBoundary -∗
  □ instr_pre 0x10190 writeOutputEntryBoundary -∗
  instr_body 0x15744
    (writeSuccessSuffixHashesBoundary
      (fun _ => writeSuccessExactPostWithdrawalsExitFrame args witness P)) -∗
  instr_body 0x156e8
    (writeSuccessExactPostWithdrawalsBoundary
      (writeSuccessFrameSp witness)
      (bv_unsigned (writeSuccessWithdrawalsBase witness))
      (writeSuccessWithdrawalsBytes witness)
      (writeSuccessExactPostWithdrawalsEvents witness)
      (writeSuccessExactPostWithdrawalsCallerFrame args witness ∗ P)).
Proof.
  have [Halign [Hbound Haddress]] := post_withdrawals_stack_facts args witness Hwf.
  have Hfirst := exact_post_withdrawals_first_tail_explicit witness.
  have Hsecond := exact_post_withdrawals_second_tail_explicit witness.
  have Hframe16 :
      (writeSuccessEntrySp witness - (BV 64 2000 + BV 64 16))%bv =
      (writeSuccessFrameSp witness - BV 64 16)%bv by
    (unfold writeSuccessFrameSp; bv_solve).
  have [Hframe [HframeAlign HframeUpper]] :=
    exact_prefix_stack_facts args witness Hwf.
  have HframeLow : 16 <= bv_unsigned (writeSuccessFrameSp witness) by
    (unfold writeSuccessWitnessWellFormed in Hwf;
     cbv [mapRamBase defaultMap] in Hwf; lia).
  have Hdelta1144 := zesu_bv_unsigned_add_Z_64
    (writeSuccessFrameSp witness) 1144
    ltac:(cbv [machineRamEnd mapRamSize mapRamBase defaultMap] in HframeUpper; lia).
  have Haddress1144 :
      bv_unsigned (writeSuccessFrameSp witness + BV 64 1144) =
      bv_unsigned (writeSuccessFrameSp witness) + 1144 by
    (change (bv_unsigned (writeSuccessFrameSp witness + Z_to_bv 64 1144) =
       bv_unsigned (writeSuccessFrameSp witness) + 1144); lia).
  have Hlookup13 : (take 69 (writeSuccessValues witness)) !! 13%nat =
      Some (writeSuccessValueWord (writeSuccessValues witness) 13%nat).
  { rewrite lookup_take; [|lia]. unfold writeSuccessValueWord.
    destruct (writeSuccessValues witness !! 13%nat) eqn:Hlookup; [reflexivity |].
    apply lookup_ge_None_1 in Hlookup.
    unfold writeSuccessWitnessWellFormed in Hwf. lia. }
  have Hlookup14 : (take 69 (writeSuccessValues witness)) !! 14%nat =
      Some (writeSuccessValueWord (writeSuccessValues witness) 14%nat).
  { rewrite lookup_take; [|lia]. unfold writeSuccessValueWord.
    destruct (writeSuccessValues witness !! 14%nat) eqn:Hlookup; [reflexivity |].
    apply lookup_ge_None_1 in Hlookup.
    unfold writeSuccessWitnessWellFormed in Hwf. lia. }
  zesu_block.
  all: repeat first [progress iIntros (?) | progress iIntros "#?" | progress iIntros "?"]; iRename select (instr_pre 0x15d10 encoderIntEntryBoundary) into "Hint"; iEval (rewrite /encoderIntEntryBoundary) in "Hint"; zesu_run.
  all: iApply find_in_context_mem_mapsto_semantic; iExists (MKArray 64 (bv_unsigned (writeSuccessFrameSp witness) + 1032) (take 69 (writeSuccessValues witness))); iFrame; zesu_run.
  all: try (rename select ((take 69 (writeSuccessValues witness)) !! _ = Some _)
    into Hloaded; rewrite Haddress in Hloaded;
    replace (Z.to_nat (((bv_unsigned (writeSuccessFrameSp witness) + 1136) -
      (bv_unsigned (writeSuccessFrameSp witness) + 1032)) `div` 8))
      with 13%nat in Hloaded by lia; rewrite Hlookup13 in Hloaded;
    injection Hloaded; intros; subst);
    try (liInst (fun x => x.1ₗ = exactPostWithdrawalsFirstTail witness); zesu_run).
  all: lazymatch goal with
  | |- (Z.to_nat ((bv_unsigned (_ + 1136) - _) `div` 8) < _)%nat => rewrite Haddress; rewrite length_take; simpl; unfold writeSuccessWitnessWellFormed in Hwf; lia
  | |- Snapshots.writeOutputEvents _ _ _ _ ⊆ _ => idtac
  | |- environments.envs_entails _ _ =>
      zesu_liAStep; try zesu_run;
      iSplit; [iIntros "Hreturn HPC";
        iEval (rewrite /WriteSuccessExactEncoderIntCall.encoderIntExactReturn) in "Hreturn";
        zesu_open_resource_groups; try zesu_run;
        iApply find_in_context_mem_mapsto_semantic;
        iExists (MKArray 64 (bv_unsigned (writeSuccessFrameSp witness) + 1032)
          (take 69 (writeSuccessValues witness))); iFrame; try zesu_run;
        lazymatch goal with
        | |- (Z.to_nat ((bv_unsigned (_ + 1144) - _) `div` 8) < _)%nat => rewrite Haddress1144; rewrite length_take; simpl; unfold writeSuccessWitnessWellFormed in Hwf; lia
        | Hloaded14 : (take 69 _) !! _ = Some _ |- _ =>
            rewrite Haddress1144 in Hloaded14;
            replace (Z.to_nat (((bv_unsigned (writeSuccessFrameSp witness) + 1144) -
              (bv_unsigned (writeSuccessFrameSp witness) + 1032)) `div` 8))
              with 14%nat in Hloaded14 by lia;
            rewrite Hlookup14 in Hloaded14; injection Hloaded14; intros; subst; try zesu_run
        | |- _ => idtac
        end;
        lazymatch goal with
        | |- scons_snap _ _ _ ⊆ _ => idtac
        | |- _ => try (liInst (fun x => x.1ₗ = writeSuccessExactPostWithdrawalsTailAt 2 witness); zesu_run)
        end;
        lazymatch goal with
        | |- scons_snap _ _ _ ⊆ _ => idtac
        | |- _ => try (liInst (fun x => x.1ₗ = writeSuccessExactPostWithdrawalsTailAt (writeSuccessExactPostWithdrawalsAfterOptionalIndex witness) witness); zesu_run)
        end;
        lazymatch goal with
        | |- scons_snap _ _ _ ⊆ _ => idtac
        | |- _ => try (liInst (fun x => x.1ₗ = writeSuccessExactPostWithdrawalsTailAt (writeSuccessExactPostWithdrawalsAfterBytesIndex witness) witness); zesu_run)
        end;
        lazymatch goal with
        | |- scons_snap _ _ _ ⊆ _ => idtac
        | |- _ => try (liInst (fun x => x.1ₗ = writeSuccessExactPostWithdrawalsTailAt (S (writeSuccessExactPostWithdrawalsAfterBytesIndex witness)) witness); zesu_run)
        end
      | done]
  end.
  all: lazymatch goal with
  | |- Snapshots.writeOutputEvents _ _ _ _ ⊆ _ =>
      rewrite Hframe16 Hfirst;
      cbn [writeSuccessPrivateBytes WriteSuccessObservation.writeSuccessEncodeU64
        WriteSuccessObservation.writeSuccessEncodeLe]; done
  | |- scons_snap _ _ _ ⊆ _ =>
      cbv [machineOutputSizeAddress defaultMap writeSuccessPrivateBytes
        WriteSuccessObservation.writeSuccessEncodeU64
        WriteSuccessObservation.writeSuccessEncodeLe];
      change (exactPostWithdrawalsSecondContinuation witness ⊆
        exactPostWithdrawalsSecondContinuation witness); done
  | |- ?G => fail 1 "GOAL" G
  end.

Qed.

Print Assumptions write_success_exact_post_withdrawals_segment.
