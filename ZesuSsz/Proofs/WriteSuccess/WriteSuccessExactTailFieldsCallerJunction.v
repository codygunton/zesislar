Require Import ZesuSsz.Automation.All.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessExactTailFieldsSourceJunction.
Require Import ZesuSsz.Automation.ArraySlices.
Require Import ZesuSsz.Contracts.IslarisMemory.
Require Import ZesuSsz.Proofs.WriteSuccess.Interfaces.
Require Import ZesuSsz.Contracts.Endpoints.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessNativeContract.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessPostTransactionResources.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessHeaderValueTransactions.
From ZesuSsz.Proofs.WriteSuccess Require Import WriteSuccessRepresentation WriteSuccessExactValueSpec WriteSuccessValueBlock WriteSuccessByteLists WriteSuccessTransactionsSpec WriteSuccessTransactionsPost15674Boundary.

Require Import isla.riscv64.riscv64.
From Coq Require Import Lists.List.
Import ListNotations.
Open Scope Z_scope.

Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessExactTailFieldsPayloadJunction.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessExactTailFieldsCopiedJunction.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessPostTransactionDescriptors.
Require Import ZesuSsz.Automation.PackedWordValues.
Lemma tail_fields_initial_descriptor_words (sp : bv 64)
    (sourceBytes decodedBytes : list (bv 8))
    (post : WriteSuccessPostTransactionData) :
  length sourceBytes = 720%nat ->
  writeSuccessPostTransactionDataFacts sp sourceBytes decodedBytes post ->
  u64s_of_bytes 2 (take 16 (drop 608 sourceBytes)) =
    [(writeSuccessPostBytes158e0 post).1; (writeSuccessPostBytes158e0 post).2].
Proof.
intros Hlength Hfacts; have Hdescriptor : writeSuccessPostBytes158e0 post = writeSuccessPostDescriptor (writeSuccessPostSourceWords sourceBytes) 76 77 by rewrite /writeSuccessPostTransactionDataFacts in Hfacts; naive_solver.
rewrite Hdescriptor /writeSuccessPostDescriptor /writeSuccessPostWord /writeSuccessPostSourceWords; cbv beta iota delta [fst snd].
apply (list_eq_same_length _ _ 2); [reflexivity|rewrite /u64s_of_bytes length_fmap length_reshape length_replicate; reflexivity|]; intros i x y Hi Hx Hy.
rewrite zesu_packed_u64_lookup in Hx; [|rewrite length_take length_drop; lia|exact Hi]; rewrite zesu_packed_window_take_drop in Hx; [|lia]; inversion Hx; subst x.
destruct i as [|[|i]]; try lia; rewrite !zesu_packed_u64_lookup in Hy; try lia; cbv beta iota delta [default list_lookup] in Hy; injection Hy as <-; reflexivity.
Qed.

Definition tailFieldsCallerRest `{!islaG Sigma} `{!threadG}
    {Decoded} `{!WriteSuccessMemoryRepresentation Decoded}
    (args : WriteSuccessArgs Decoded)
    (witness : writeSuccessNativeWitness Decoded) : iProp Sigma :=
  let sp := writeSuccessFrameSp witness in
  let values := writeSuccessValues witness in
  (tailFieldsSourceUntouched (bv_unsigned sp + 312) (writeSuccessSourceBytes witness) ∗
   tailFieldsCopiedUntouched sp (writeSuccessDecodedBytes witness) ∗
   bv_unsigned sp ↦ₘ? 8 ∗
   writeSuccessExactValueMemory sp values ∗
   (bv_unsigned sp + 1624) ↦ₘ? 16 ∗
   writeSuccessTerminalSavedSlots witness ∗
   bv_unsigned (writeSuccessDecodedPointer witness) ↦ₘ∗ writeSuccessDecodedBytes witness ∗
   bv_unsigned (writeSuccessValueWord values 4) ↦ₘ∗ writeSuccessPayload witness ∗
   byteListItemResources (bv_unsigned (writeSuccessValueWord values 9))
     (writeSuccessRawTransactions witness) ∗
   bv_unsigned (writeSuccessWithdrawalsBase witness) ↦ₘ∗ writeSuccessWithdrawalsBytes witness ∗
   tailFieldsInactivePayloads sp (writeSuccessSourceBytes witness)
     (writeSuccessDecodedBytes witness) (writeSuccessPostData witness) ∗
   writeSuccessNativeStaticResources ∗
   writeSuccessTransactionsInvariant sp (writeSuccessTransactionBase witness)
     (writeSuccessTransactions witness) [] (writeSuccessTransactions witness)
     (WriteSuccessNativeContract.writeSuccessTransactionBytes witness) [] (WriteSuccessNativeContract.writeSuccessTransactionBytes witness) ∗
   ⌜writeSuccessWitnessWellFormed args witness⌝ ∗ True)%I.



Lemma tailFieldsCallerRest_unfold `{!islaG Sigma} `{!threadG}
    {Decoded} `{!WriteSuccessMemoryRepresentation Decoded}
    (args : WriteSuccessArgs Decoded)
    (witness : writeSuccessNativeWitness Decoded) :
  tailFieldsCallerRest args witness ⊣⊢
let sp := writeSuccessFrameSp witness in
  let values := writeSuccessValues witness in
  (tailFieldsSourceUntouched (bv_unsigned sp + 312) (writeSuccessSourceBytes witness) ∗
   tailFieldsCopiedUntouched sp (writeSuccessDecodedBytes witness) ∗
   bv_unsigned sp ↦ₘ? 8 ∗
   writeSuccessExactValueMemory sp values ∗
   (bv_unsigned sp + 1624) ↦ₘ? 16 ∗
   writeSuccessTerminalSavedSlots witness ∗
   bv_unsigned (writeSuccessDecodedPointer witness) ↦ₘ∗ writeSuccessDecodedBytes witness ∗
   bv_unsigned (writeSuccessValueWord values 4) ↦ₘ∗ writeSuccessPayload witness ∗
   byteListItemResources (bv_unsigned (writeSuccessValueWord values 9))
     (writeSuccessRawTransactions witness) ∗
   bv_unsigned (writeSuccessWithdrawalsBase witness) ↦ₘ∗ writeSuccessWithdrawalsBytes witness ∗
   tailFieldsInactivePayloads sp (writeSuccessSourceBytes witness)
     (writeSuccessDecodedBytes witness) (writeSuccessPostData witness) ∗
   writeSuccessNativeStaticResources ∗
   writeSuccessTransactionsInvariant sp (writeSuccessTransactionBase witness)
     (writeSuccessTransactions witness) [] (writeSuccessTransactions witness)
     (WriteSuccessNativeContract.writeSuccessTransactionBytes witness) [] (WriteSuccessNativeContract.writeSuccessTransactionBytes witness) ∗
   ⌜writeSuccessWitnessWellFormed args witness⌝ ∗ True)%I.
Proof. done. Qed.
Global Opaque tailFieldsCallerRest.

Definition tailFieldsCallerPrepared `{!islaG Sigma} `{!threadG}
    {Decoded} `{!WriteSuccessMemoryRepresentation Decoded}
    (args : WriteSuccessArgs Decoded)
    (witness : writeSuccessNativeWitness Decoded) : iProp Sigma :=
  let sp := writeSuccessFrameSp witness in
  let post := writeSuccessPostData witness in
  ((bv_unsigned sp - 80) ↦ₘ? 32 ∗
   (bv_unsigned sp + 920) ↦ₘ∗ [(writeSuccessPostBytes158e0 post).1; (writeSuccessPostBytes158e0 post).2] ∗
   (bv_unsigned sp + 936) ↦ₘ∗ tailFieldsDescriptorWords post ∗
   (bv_unsigned sp + 16) ↦ₘ∗ tailFieldsCopiedWords (writeSuccessDecodedBytes witness) ∗
   writeSuccessDescriptorResources (writeSuccessPostBytes158e0 post) (writeSuccessPostBytes158e0Payload post) ∗
   tailFieldsActivePayloads (writeSuccessDecodedBytes witness) post ∗
   tailFieldsCallerRest args witness ∗ True)%I.

Global Instance : LithiumUnfold (@tailFieldsCallerPrepared) := I.

Lemma tail_fields_caller_junction_with_facts `{!islaG Sigma} `{!threadG}
    {Decoded} `{!WriteSuccessMemoryRepresentation Decoded}
    (args : WriteSuccessArgs Decoded)
    (witness : writeSuccessNativeWitness Decoded) :
  writeSuccessWitnessWellFormed args witness ->
  writeSuccessPostTransactionDataFacts (writeSuccessFrameSp witness)
    (writeSuccessSourceBytes witness) (writeSuccessDecodedBytes witness) (writeSuccessPostData witness) ->
  writeSuccessExactTailCallerBundle args witness ⊣⊢ tailFieldsCallerPrepared args witness.
Proof.
intros Hwf Hfacts; have Hlength : length (writeSuccessSourceBytes witness) = 720%nat by rewrite /writeSuccessWitnessWellFormed in Hwf; naive_solver.
rewrite (tail_fields_caller_source_junction args witness Hwf) /tailFieldsCallerSourceView /tailFieldsSourceWordView tail_fields_caller_payload_junction /tailFieldsCallerInactive tail_fields_copied_junction /tailFieldsCallerPrepared tailFieldsCallerRest_unfold; cbv beta zeta.
rewrite (tail_fields_initial_descriptor_words _ _ _ _ Hlength Hfacts) (tail_fields_descriptor_words _ _ _ _ Hlength Hfacts) -!Z.add_assoc; change (312 + 608) with 920; change (312 + 624) with 936.
iSplit; [iIntros "((Hfirst & Hd & Hsource & _) & (Hpayload & Hactive & (Hscratch & Hsp & (Hcopied & Hcopyrest & _) & Hrest) & _) & _)" | iIntros "(Hscratch & Hfirst & Hd & Hcopied & Hpayload & Hactive & (Hsource & Hcopyrest & Hsp & Hrest) & _)"]; iFrame.
Qed.

Lemma tail_fields_post_resource_facts `{!islaG Sigma} `{!threadG}
    (sp : bv 64) (sourceBytes decodedBytes : list (bv 8))
    (post : WriteSuccessPostTransactionData) :
  writeSuccessPostTransactionDataResources sp sourceBytes decodedBytes post -∗
  writeSuccessPostTransactionDataResources sp sourceBytes decodedBytes post ∗
  ⌜writeSuccessPostTransactionDataFacts sp sourceBytes decodedBytes post⌝.
Proof.
rewrite /writeSuccessPostTransactionDataResources; cbv beta zeta; iIntros "(H0 & H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8 & H9 & H10 & H11 & %Hfacts)".
iFrame "∗%".
Qed.

Lemma tail_fields_caller_facts `{!islaG Sigma} `{!threadG}
    {Decoded} `{!WriteSuccessMemoryRepresentation Decoded}
    (args : WriteSuccessArgs Decoded) (witness : writeSuccessNativeWitness Decoded) :
  writeSuccessExactTailCallerBundle args witness -∗
  writeSuccessExactTailCallerBundle args witness ∗
  ⌜writeSuccessPostTransactionDataFacts (writeSuccessFrameSp witness)
    (writeSuccessSourceBytes witness) (writeSuccessDecodedBytes witness) (writeSuccessPostData witness)⌝.
Proof.
rewrite writeSuccessExactTailCallerBundle_unfold /writeSuccessExactTailCallerWithCopiedWords; cbv beta zeta; iIntros "(H0 & H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8 & H9 & H10 & Hpost & H12 & H13 & H14 & _)".
iDestruct (tail_fields_post_resource_facts with "Hpost") as "(Hpost & %Hfacts)".
iFrame "∗%".
Qed.

Lemma tail_fields_prepared_facts `{!islaG Sigma} `{!threadG}
    {Decoded} `{!WriteSuccessMemoryRepresentation Decoded}
    (args : WriteSuccessArgs Decoded) (witness : writeSuccessNativeWitness Decoded) :
  tailFieldsCallerPrepared args witness -∗ tailFieldsCallerPrepared args witness ∗
  ⌜writeSuccessPostTransactionDataFacts (writeSuccessFrameSp witness)
    (writeSuccessSourceBytes witness) (writeSuccessDecodedBytes witness) (writeSuccessPostData witness)⌝.
Proof.
rewrite /tailFieldsCallerPrepared tailFieldsCallerRest_unfold; cbv beta zeta; rewrite tailFieldsInactivePayloads_unfold.
iIntros "(Hscratch & Hfirst & Hd & Hcopied & Hpayload & Hactive & (Hsource & Hcopyrest & H0 & H1 & H2 & H3 & H4 & H5 & H6 & H7 & (Hp0 & Hp1 & Hp2 & Hp3 & %Hfacts & _) & H8 & H9 & H10 & _) & _)".
iFrame "∗%".
Qed.

Lemma tail_fields_caller_junction `{!islaG Sigma} `{!threadG}
    {Decoded} `{!WriteSuccessMemoryRepresentation Decoded}
    (args : WriteSuccessArgs Decoded) (witness : writeSuccessNativeWitness Decoded) :
  writeSuccessWitnessWellFormed args witness ->
  writeSuccessExactTailCallerBundle args witness ⊣⊢ tailFieldsCallerPrepared args witness.
Proof.
  intros Hwf; iSplit; iIntros "Hcaller".
  - iDestruct (tail_fields_caller_facts with "Hcaller") as "(Hcaller & %Hfacts)"; rewrite -(tail_fields_caller_junction_with_facts args witness Hwf Hfacts); iExact "Hcaller".
  - iDestruct (tail_fields_prepared_facts with "Hcaller") as "(Hcaller & %Hfacts)"; rewrite (tail_fields_caller_junction_with_facts args witness Hwf Hfacts); iExact "Hcaller".
Qed.

Print Assumptions tail_fields_caller_junction.
