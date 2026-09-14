Require Import ZesuSsz.Automation.All.
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Contracts.Endpoints.
Require Import ZesuSsz.Contracts.IslarisMemory.
From ZesuSsz.Proofs.WriteSuccess Require Import WriteSuccessNativeContract
 WriteSuccessValueBlock WriteSuccessExactTransactionsLiveSpec WriteSuccessRepresentation.
Lemma exact_prefix_witness_facts {Decoded} `{!WriteSuccessMemoryRepresentation Decoded}
    (args : WriteSuccessArgs Decoded) (witness : writeSuccessNativeWitness Decoded)
    (Hwf : writeSuccessWitnessWellFormed args witness)
    (Hfacts : transactionLoopSourceFacts (writeSuccessFrameSp witness)
      (writeSuccessTransactionBase witness) (writeSuccessTransactions witness) []
      (writeSuccessTransactions witness) (writeSuccessTransactionBytes witness)) :
  bv_unsigned (writeSuccessValueWord (writeSuccessValues witness) 5) =
    Z.of_nat (length (writeSuccessPayload witness)) /\
  bv_unsigned (writeSuccessValueWord (writeSuccessValues witness) 8) =
    Z.of_nat (length (writeSuccessTransactions witness)) /\
  bytes_of_u64s (writeSuccessValues witness) =
    take 592 (take 720 (writeSuccessDecodedBytes witness)).
Proof.
  unfold writeSuccessWitnessWellFormed in Hwf.
  unfold transactionLoopSourceFacts in Hfacts.
  have Hbound : (length (writeSuccessTransactions witness) < 2 ^ 64)%nat by tauto.
  have Hword : writeSuccessValueWord (writeSuccessValues witness) 8 =
      Z_to_bv 64 (Z.of_nat (length (writeSuccessTransactions witness))) by tauto.
  have HboundZ := (proj1 (Nat2Z.inj_lt _ _)) Hbound.
  rewrite Nat2Z.inj_pow in HboundZ.
  have Hrange : 0 <= Z.of_nat (length (writeSuccessTransactions witness)) < bv_modulus 64.
  { split; [apply Nat2Z.is_nonneg | exact HboundZ]. }
  split; [tauto |]. split.
  - rewrite Hword. apply Z_to_bv_small. exact Hrange.
  - have Hsource : writeSuccessSourceBytes witness = take 720 (writeSuccessDecodedBytes witness) by tauto.
    rewrite -Hsource. tauto.
Qed.
Print Assumptions exact_prefix_witness_facts.
