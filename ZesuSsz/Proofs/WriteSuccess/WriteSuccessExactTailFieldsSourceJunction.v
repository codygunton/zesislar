Require Import ZesuSsz.Automation.All.
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

Definition tailFieldsSourceByteView `{!islaG Sigma}
    (base : Z) (bytes : list (bv 8)) : iProp Sigma :=
  (base ↦ₘ∗ take 608 bytes ∗
   (base + 608) ↦ₘ∗ take 16 (drop 608 bytes) ∗
   (base + 624) ↦ₘ∗ take 64 (drop 624 bytes) ∗
   (base + 688) ↦ₘ∗ drop 688 bytes ∗ True)%I.

Lemma tail_fields_source_bytes_open `{!islaG Sigma}
    (base : Z) (bytes : list (bv 8)) :
  length bytes = 720%nat ->
  base ↦ₘ∗ bytes -∗ tailFieldsSourceByteView base bytes.
Proof.
  iIntros (Hlength) "Hbytes".
  iDestruct (mem_mapsto_array_region 8 base (DfracOwn 1) bytes 608 16 ltac:(lia) with "Hbytes") as "(Hprefix & Hfirst & Hrest)".
  iDestruct (mem_mapsto_array_region 8 (base + 624) (DfracOwn 1) (drop 624 bytes) 0 64 ltac:(rewrite length_drop Hlength; lia) with "[Hrest]") as "(_ & Hdescriptors & Hsuffix)"; first (cbn; rewrite Z.mul_1_l; iExact "Hrest").
  rewrite /tailFieldsSourceByteView; iEval (cbn; rewrite ?Z.mul_1_l ?Z.add_0_r ?drop_drop) in "Hprefix Hfirst Hdescriptors Hsuffix".
  replace (base + 624 + 64) with (base + 688) by lia; iFrame.
Qed.

Lemma tail_fields_source_bytes_close `{!islaG Sigma}
    (base : Z) (bytes : list (bv 8)) :
  length bytes = 720%nat ->
  tailFieldsSourceByteView base bytes -∗ base ↦ₘ∗ bytes.
Proof.
  iIntros (Hlength) "(Hprefix & Hfirst & Hdescriptors & Hsuffix & _)".
  iPoseProof (mem_mapsto_array_app_combine_at 8 (base + 624) (DfracOwn 1) (take 64 (drop 624 bytes)) (drop 64 (drop 624 bytes)) 64 ltac:(rewrite length_take length_drop Hlength; lia) with "Hdescriptors [Hsuffix]") as "Hrest".
  { cbn; rewrite Z.mul_1_l drop_drop; replace (base + 624 + 64) with (base + 688) by lia; iExact "Hsuffix". }
  iEval (rewrite take_drop) in "Hrest".
  iApply (mem_array_slice_restore base bytes 608 16 ltac:(lia) with "Hprefix Hfirst Hrest").
Qed.

Definition tailFieldsSourceUntouched `{!islaG Sigma}
    (base : Z) (bytes : list (bv 8)) : iProp Sigma :=
  (base ↦ₘ∗ take 608 bytes ∗
   (base + 688) ↦ₘ∗ drop 688 bytes ∗ True)%I.

Lemma tailFieldsSourceUntouched_unfold `{!islaG Sigma}
    (base : Z) (bytes : list (bv 8)) :
  tailFieldsSourceUntouched base bytes ⊣⊢
  (base ↦ₘ∗ take 608 bytes ∗
   (base + 688) ↦ₘ∗ drop 688 bytes ∗ True)%I.
Proof. done. Qed.
Global Opaque tailFieldsSourceUntouched.

Definition tailFieldsSourceWordView `{!islaG Sigma}
    (base : Z) (bytes : list (bv 8)) : iProp Sigma :=
  ((base + 608) ↦ₘ∗ u64s_of_bytes 2 (take 16 (drop 608 bytes)) ∗
   (base + 624) ↦ₘ∗ u64s_of_bytes 8 (take 64 (drop 624 bytes)) ∗
   tailFieldsSourceUntouched base bytes ∗ True)%I.

Lemma tail_fields_source_byte_word_equiv `{!islaG Sigma}
    (base : Z) (bytes : list (bv 8)) (count : nat) :
  length bytes = (count * 8)%nat ->
  base ↦ₘ∗ bytes ⊣⊢ base ↦ₘ∗ u64s_of_bytes count bytes.
Proof.
  intros Hlength; iSplit; iIntros "Hbytes".
  - iApply mem_mapsto_bytes_to_u64_array; rewrite (bytes_of_u64s_of_bytes count bytes Hlength); iExact "Hbytes".
  - iPoseProof (mem_mapsto_u64_array_to_bytes with "Hbytes") as "Hbytes"; rewrite (bytes_of_u64s_of_bytes count bytes Hlength); iExact "Hbytes".
Qed.

Lemma tail_fields_source_views_equiv `{!islaG Sigma}
    (base : Z) (bytes : list (bv 8)) :
  length bytes = 720%nat ->
  tailFieldsSourceByteView base bytes ⊣⊢ tailFieldsSourceWordView base bytes.
Proof.
  intros Hlength; rewrite /tailFieldsSourceByteView /tailFieldsSourceWordView tailFieldsSourceUntouched_unfold.
  rewrite (tail_fields_source_byte_word_equiv (base + 608) (take 16 (drop 608 bytes)) 2 ltac:(rewrite length_take length_drop Hlength; lia)).
  rewrite (tail_fields_source_byte_word_equiv (base + 624) (take 64 (drop 624 bytes)) 8 ltac:(rewrite length_take length_drop Hlength; lia)).
  iSplit; [iIntros "(H0 & H1 & H2 & H3 & _)" | iIntros "(H1 & H2 & (H0 & H3 & _) & _)"]; iFrame.
Qed.

Lemma tail_fields_source_junction_open `{!islaG Sigma}
    (base : Z) (bytes : list (bv 8)) :
  length bytes = 720%nat ->
  base ↦ₘ∗ bytes -∗ tailFieldsSourceWordView base bytes.
Proof.
  intros Hlength; rewrite -(tail_fields_source_views_equiv base bytes Hlength).
  apply tail_fields_source_bytes_open; done.
Qed.

Lemma tail_fields_source_junction_close `{!islaG Sigma}
    (base : Z) (bytes : list (bv 8)) :
  length bytes = 720%nat ->
  tailFieldsSourceWordView base bytes -∗ base ↦ₘ∗ bytes.
Proof.
  intros Hlength; rewrite -(tail_fields_source_views_equiv base bytes Hlength).
  apply tail_fields_source_bytes_close; done.
Qed.

Print Assumptions tail_fields_source_junction_open.
Print Assumptions tail_fields_source_junction_close.

Definition tailFieldsCallerUntouched `{!islaG Sigma} `{!threadG}
    {Decoded} `{!WriteSuccessMemoryRepresentation Decoded}
    (args : WriteSuccessArgs Decoded)
    (witness : writeSuccessNativeWitness Decoded) : iProp Sigma :=
  let sp := writeSuccessFrameSp witness in
  let values := writeSuccessValues witness in
  ((bv_unsigned sp - 80) ↦ₘ? 32 ∗
   bv_unsigned sp ↦ₘ? 8 ∗
   writeSuccessExactCopiedTailWords sp (writeSuccessDecodedBytes witness) ∗
   writeSuccessExactValueMemory sp values ∗
   (bv_unsigned sp + 1624) ↦ₘ? 16 ∗
   writeSuccessTerminalSavedSlots witness ∗
   bv_unsigned (writeSuccessDecodedPointer witness) ↦ₘ∗ writeSuccessDecodedBytes witness ∗
   bv_unsigned (writeSuccessValueWord values 4) ↦ₘ∗ writeSuccessPayload witness ∗
   byteListItemResources (bv_unsigned (writeSuccessValueWord values 9))
     (writeSuccessRawTransactions witness) ∗
   bv_unsigned (writeSuccessWithdrawalsBase witness) ↦ₘ∗ writeSuccessWithdrawalsBytes witness ∗
   writeSuccessPostTransactionDataResources sp (writeSuccessSourceBytes witness)
     (writeSuccessDecodedBytes witness) (writeSuccessPostData witness) ∗
   writeSuccessNativeStaticResources ∗
   writeSuccessTransactionsInvariant sp (writeSuccessTransactionBase witness)
     (writeSuccessTransactions witness) [] (writeSuccessTransactions witness)
     (WriteSuccessNativeContract.writeSuccessTransactionBytes witness) [] (WriteSuccessNativeContract.writeSuccessTransactionBytes witness) ∗
   ⌜writeSuccessWitnessWellFormed args witness⌝ ∗ True)%I.

Lemma tailFieldsCallerUntouched_unfold `{!islaG Sigma} `{!threadG}
    {Decoded} `{!WriteSuccessMemoryRepresentation Decoded}
    (args : WriteSuccessArgs Decoded)
    (witness : writeSuccessNativeWitness Decoded) :
  tailFieldsCallerUntouched args witness ⊣⊢
  let sp := writeSuccessFrameSp witness in
  let values := writeSuccessValues witness in
  ((bv_unsigned sp - 80) ↦ₘ? 32 ∗
   bv_unsigned sp ↦ₘ? 8 ∗
   writeSuccessExactCopiedTailWords sp (writeSuccessDecodedBytes witness) ∗
   writeSuccessExactValueMemory sp values ∗
   (bv_unsigned sp + 1624) ↦ₘ? 16 ∗
   writeSuccessTerminalSavedSlots witness ∗
   bv_unsigned (writeSuccessDecodedPointer witness) ↦ₘ∗ writeSuccessDecodedBytes witness ∗
   bv_unsigned (writeSuccessValueWord values 4) ↦ₘ∗ writeSuccessPayload witness ∗
   byteListItemResources (bv_unsigned (writeSuccessValueWord values 9))
     (writeSuccessRawTransactions witness) ∗
   bv_unsigned (writeSuccessWithdrawalsBase witness) ↦ₘ∗ writeSuccessWithdrawalsBytes witness ∗
   writeSuccessPostTransactionDataResources sp (writeSuccessSourceBytes witness)
     (writeSuccessDecodedBytes witness) (writeSuccessPostData witness) ∗
   writeSuccessNativeStaticResources ∗
   writeSuccessTransactionsInvariant sp (writeSuccessTransactionBase witness)
     (writeSuccessTransactions witness) [] (writeSuccessTransactions witness)
     (WriteSuccessNativeContract.writeSuccessTransactionBytes witness) [] (WriteSuccessNativeContract.writeSuccessTransactionBytes witness) ∗
   ⌜writeSuccessWitnessWellFormed args witness⌝ ∗ True)%I.
Proof. done. Qed.
Global Opaque tailFieldsCallerUntouched.

Definition tailFieldsCallerSourceView `{!islaG Sigma} `{!threadG}
    {Decoded} `{!WriteSuccessMemoryRepresentation Decoded}
    (args : WriteSuccessArgs Decoded)
    (witness : writeSuccessNativeWitness Decoded) : iProp Sigma :=
  (tailFieldsSourceWordView
      (bv_unsigned (writeSuccessFrameSp witness) + 312)
      (writeSuccessSourceBytes witness) ∗
   tailFieldsCallerUntouched args witness ∗ True)%I.

Lemma tail_fields_source_junction_equiv `{!islaG Sigma}
    (base : Z) (bytes : list (bv 8)) :
  length bytes = 720%nat ->
  base ↦ₘ∗ bytes ⊣⊢ tailFieldsSourceWordView base bytes.
Proof.
  intros Hlength; iSplit.
  - iApply tail_fields_source_junction_open; done.
  - iApply tail_fields_source_junction_close; done.
Qed.

Lemma tail_fields_caller_source_junction `{!islaG Sigma} `{!threadG}
    {Decoded} `{!WriteSuccessMemoryRepresentation Decoded}
    (args : WriteSuccessArgs Decoded)
    (witness : writeSuccessNativeWitness Decoded) :
  writeSuccessWitnessWellFormed args witness ->
  writeSuccessExactTailCallerBundle args witness ⊣⊢
  tailFieldsCallerSourceView args witness.
Proof.
  intros Hwf; have Hlength : length (writeSuccessSourceBytes witness) = 720%nat by rewrite /writeSuccessWitnessWellFormed in Hwf; naive_solver.
  rewrite /tailFieldsCallerSourceView -(tail_fields_source_junction_equiv _ _ Hlength).
  rewrite writeSuccessExactTailCallerBundle_unfold /writeSuccessExactTailCallerWithCopiedWords tailFieldsCallerUntouched_unfold /=.
  iSplit; [iIntros "(H0 & H1 & H2 & Hsource & Hrest)" | iIntros "(Hsource & (H0 & H1 & H2 & Hrest) & _)"]; iFrame.
Qed.
Print Assumptions tail_fields_caller_source_junction.
