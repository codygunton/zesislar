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
Definition tailFieldsListsCallerReturn `{!islaG Sigma} `{!threadG}
    {Decoded} `{!WriteSuccessMemoryRepresentation Decoded}
    (args : WriteSuccessArgs Decoded) (witness : writeSuccessNativeWitness Decoded)
    (oldS1 : bv 64) (tail : spec) : iProp Sigma :=
  let sp := writeSuccessFrameSp witness in
  (exactSuffixBytesPayloadEntryRegisters sp (BV 64 0) oldS1 ∗
   reg_col ((fun register => (KindReg register, BitsShape 64)) <$> exactSuffixBytesOtherRegisters) ∗
   (bv_unsigned sp - 48) ↦ₘ? 48 ∗
   mmio_range (machineOutputAddress defaultMap) 16 ∗ spec_trace tail ∗
   ⌜bv_unsigned sp `mod` 16 = 0 /\ mapRamBase defaultMap <= bv_unsigned sp - 80 /\
     bv_unsigned sp + 1896 < machineRamEnd defaultMap⌝ ∗
   tailFieldsCallerPrepared args witness ∗ True)%I.
Global Instance : LithiumUnfold (@tailFieldsListsCallerReturn) := I.

Lemma tail_fields_bytes_scratch_to_uninit `{!islaG Sigma}
    (sp : Z) (bytes : list (bv 8)) (w1 w2 w3 w4 w5 : bv 64) :
  length bytes = 8%nat ->
  (sp - 48) ↦ₘ∗ bytes -∗ (sp - 40) ↦ₘ w1 -∗ (sp - 32) ↦ₘ w2 -∗
  (sp - 24) ↦ₘ w3 -∗ (sp - 16) ↦ₘ w4 -∗ (sp - 8) ↦ₘ w5 -∗
  (sp - 48) ↦ₘ? 48.
Proof.
  iIntros (Hlength) "H0 H1 H2 H3 H4 H5".
  iDestruct (mem_mapsto_byte_array_to_mapsto_len 8 with "H0") as "H0"; [done|].
  iDestruct (mem_mapsto_mapsto_to_uninit with "H0") as "H0".
  iDestruct (mem_mapsto_mapsto_to_uninit with "H1") as "H1".
  iDestruct (mem_mapsto_mapsto_to_uninit with "H2") as "H2".
  iDestruct (mem_mapsto_mapsto_to_uninit with "H3") as "H3".
  iDestruct (mem_mapsto_mapsto_to_uninit with "H4") as "H4".
  iDestruct (mem_mapsto_mapsto_to_uninit with "H5") as "H5".
  iApply (mem_mapsto_uninit_combine 8 with "H0"); [lia|].
  replace (sp - 48 + 8) with (sp - 40) by lia.
  iApply (mem_mapsto_uninit_combine 8 with "H1"); [lia|].
  replace (sp - 40 + 8) with (sp - 32) by lia.
  iApply (mem_mapsto_uninit_combine 8 with "H2"); [lia|].
  replace (sp - 32 + 8) with (sp - 24) by lia.
  iApply (mem_mapsto_uninit_combine 8 with "H3"); [lia|].
  replace (sp - 24 + 8) with (sp - 16) by lia.
  iApply (mem_mapsto_uninit_combine 8 with "H4"); [lia|].
  replace (sp - 16 + 8) with (sp - 8) by lia.
  iExact "H5".
Qed.
Print Assumptions tail_fields_bytes_scratch_to_uninit.

Lemma tail_fields_rest_facts `{!islaG Sigma} `{!threadG}
    {Decoded} `{!WriteSuccessMemoryRepresentation Decoded}
    (args : WriteSuccessArgs Decoded) (witness : writeSuccessNativeWitness Decoded) :
  tailFieldsCallerRest args witness -∗ tailFieldsCallerRest args witness ∗
  ⌜writeSuccessPostTransactionDataFacts (writeSuccessFrameSp witness)
    (writeSuccessSourceBytes witness) (writeSuccessDecodedBytes witness) (writeSuccessPostData witness)⌝.
Proof.
  rewrite tailFieldsCallerRest_unfold; cbv beta zeta; rewrite tailFieldsInactivePayloads_unfold.
  iIntros "(Hsource & Hcopyrest & H0 & H1 & H2 & H3 & H4 & H5 & H6 & H7 & (Hp0 & Hp1 & Hp2 & Hp3 & %Hfacts & _) & H8 & H9 & H10 & _)".
  iFrame "∗%".
Qed.
Print Assumptions tail_fields_rest_facts.

Lemma tail_fields_prepared_well_formed `{!islaG Sigma} `{!threadG}
    {Decoded} `{!WriteSuccessMemoryRepresentation Decoded}
    (args : WriteSuccessArgs Decoded) (witness : writeSuccessNativeWitness Decoded) :
  tailFieldsCallerPrepared args witness -∗ tailFieldsCallerPrepared args witness ∗
  ⌜writeSuccessWitnessWellFormed args witness⌝.
Proof.
  rewrite /tailFieldsCallerPrepared tailFieldsCallerRest_unfold; cbv beta zeta.
  iIntros "(Hscratch & Hfirst & Hd & Hcopied & Hpayload & Hactive & (Hsource & Hcopyrest & H0 & H1 & H2 & H3 & H4 & H5 & H6 & H7 & Hpost & H8 & H9 & %Hwf & _) & _)".
  iFrame "∗%".
Qed.

Lemma tail_fields_prepared_branch_memory `{!islaG Sigma} `{!threadG}
    {Decoded} `{!WriteSuccessMemoryRepresentation Decoded}
    (args : WriteSuccessArgs Decoded) (witness : writeSuccessNativeWitness Decoded) :
  tailFieldsCallerPrepared args witness -∗
  (bv_unsigned (writeSuccessFrameSp witness) - 48) ↦ₘ? 32 -∗
  (bv_unsigned (writeSuccessFrameSp witness) + 72) ↦ₘ
    writeSuccessPostWord (writeSuccessPostTailWords (writeSuccessDecodedBytes witness)) 7 ∗
  writeSuccessExactPostWithdrawalsMemoryFrame args witness.
Proof.
  iIntros "Hcaller Hstack".
  iDestruct (tail_fields_prepared_well_formed with "Hcaller") as "[Hcaller %Hwf]".
  iEval (rewrite -(tail_fields_caller_junction args witness Hwf)) in "Hcaller".
  iEval (rewrite writeSuccessExactTailCallerBundle_unfold /writeSuccessExactTailCallerWithCopiedWords) in "Hcaller".
  repeat iDestruct select (_ ∗ _)%I as "[? ?]".
  iDestruct select (writeSuccessExactCopiedTailWords _ _) as "Hcopied".
  iEval (unfold writeSuccessExactCopiedTailWords) in "Hcopied".
  repeat iDestruct select (_ ∗ _)%I as "[? ?]".
  iEval (unfold writeSuccessExactPostWithdrawalsMemoryFrame, writeSuccessExactCopiedTailWordsWithout7).
  iDestruct select (writeSuccessTerminalSavedSlots _) as "Hslots".
  iEval (unfold writeSuccessTerminalSavedSlots) in "Hslots"; repeat iDestruct select (_ ∗ _)%I as "[? ?]".
  iFrame "∗%".
Qed.
Print Assumptions tail_fields_prepared_branch_memory.
