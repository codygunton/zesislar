Require Import ZesuSsz.Automation.All.
Require Import ZesuSsz.Automation.Sets.v2.
Require Import ZesuSsz.Proofs.WriteSuccess.InterfacesCoverage.
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
  zesu_block.
Qed.

Print Assumptions write_success_exact_post_withdrawals_segment.
