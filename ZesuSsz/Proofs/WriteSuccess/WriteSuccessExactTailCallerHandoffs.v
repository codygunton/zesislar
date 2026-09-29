Require Import ZesuSsz.Automation.All.
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Contracts.IslarisMemory.
From ZesuSsz.Proofs.WriteSuccess Require Import
  Interfaces WriteSuccessNativeContract WriteSuccessPostTransactionResources.
From Coq Require Import Lia.

Lemma exact_tail_second_optional_words_handoff `{!islaG Sigma}
    {Decoded} (witness : writeSuccessNativeWitness Decoded) (P : iProp Sigma) :
  let sp := writeSuccessFrameSp witness in
  let words := writeSuccessPostTailWords (writeSuccessDecodedBytes witness) in
  (bv_unsigned sp + 280) ↦ₘ writeSuccessPostWord words 12 ∗
  (bv_unsigned sp + 288) ↦ₘ writeSuccessPostWord words 13 ∗ P -∗
  (bv_unsigned sp + 280) ↦ₘ∗ bytes_of_u64s
    [writeSuccessPostWord words 12; writeSuccessPostWord words 13] ∗ P.
Proof.
  cbn zeta. iIntros "(Hlow & Hhigh & HP)".
  iEval (rewrite -mem_mapsto_array_singleton) in "Hlow Hhigh".
  iPoseProof (mem_mapsto_array_app_combine 64
    (bv_unsigned (writeSuccessFrameSp witness) + 280) (DfracOwn 1) [_] [_]
    with "Hlow [Hhigh]") as "Hwords".
  { cbn. replace (bv_unsigned (writeSuccessFrameSp witness) + 280 + 8 * 1)%Z
      with (bv_unsigned (writeSuccessFrameSp witness) + 288)%Z by lia.
    iExact "Hhigh". }
  iPoseProof (mem_mapsto_u64_array_to_bytes with "Hwords") as "Hbytes".
  iFrame.
Qed.

Print Assumptions exact_tail_second_optional_words_handoff.
