Require Import ZesuSsz.Automation.AllLegacy.
Require Import ZesuMachineMap.Machine.
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Export.Snapshots.
From ZesuSsz.Proofs.WriteSuccess Require Import
  WriteSuccessNativeCode WriteSuccessExactTransactionsIndexTypeOutputRegion
  WriteSuccessExactTransactionsTypeToChainSome WriteSuccessExactTransactionsChainSomeAccessRegion
  WriteSuccessExactTransactionsSourceFieldEvents WriteSuccessExactTransactionsSourceFieldLayout
  WriteSuccessExactTransactionsChainWordImage WriteSuccessExactTransactionsIndexCell
  WriteSuccessExactTransactionsIndexSourceEntry WriteSuccessExactTransactionsGasLoads
  WriteSuccessExactBooleanSpec WriteSuccessObservation WriteSuccessOutputSemantic.

Lemma transactions_source_chain_some_region_correct `{!islaG Sigma} `{!threadG}
    (sp olddata : bv 64) (base : Z) (bytes : list (bv 8)) (processed : nat)
    dataBytes accessBytes entries tail (Q : iProp Sigma) :
  bv_extract 0 8 (transactionRowWord bytes (288 * processed) 168) <> BV 8 0 ->
  bv_unsigned sp `mod` 16 = 0 ->
  (mapRamBase defaultMap) <= bv_unsigned sp - 48 ->
  bv_unsigned sp + 1896 < (machineRamEnd defaultMap) ->
  writeSuccessCompleteNativeCode -∗
  □ instr_pre 0x153d0 (transactionSourceFieldPost sp base bytes processed (288 * processed)
    dataBytes accessBytes
    (transactionChainWordImage (transactionRowWord bytes (288 * processed) 160)
      (transactionRowWord bytes (288 * processed) 168)) entries tail Q) -∗
  instr_body 0x14f08 (transactionIndexCellEntry sp (Z_to_bv 64 base)
    (Z_to_bv 64 (Z.of_nat processed)) olddata
    (transactionIndexSourceCaller sp base bytes processed
      (writeOutputEvents (sp - BV 64 25)%bv (BV 64 1) (writeSuccessBooleanWordPayload (BV 64 1))
        (writeOutputEvents (sp - BV 64 16)%bv (BV 64 8)
          (writeSuccessPrivateBytes (writeSuccessEncodeU64
            (bv_unsigned (transactionRowWord bytes (288 * processed) 160))))
          (transactionSourceAfterChainEvents sp bytes (288 * processed) dataBytes entries tail)))
      ((bv_unsigned sp - 48) ↦ₘ? 48 ∗
        transactionFieldSourceHeap bytes (288 * processed) dataBytes accessBytes entries ∗ Q ∗ True)%I)).
Proof.
  intros Htag Halign Hlow Hhigh. iStartProof. iIntros "#Hcode #Hnext".
  iEval (unfold transactionSourceFieldPost) in "Hnext".
  iPoseProof (transactions_chain_some_access_region_correct with "Hcode Hnext") as "Hfields".
  iApply (transactions_index_type_output_region_correct with "Hcode").
  iApply (instr_pre_wand 0x150f0 0x150f0 false false with "Hfields"); [done | done |].
  iIntros "Hpost". iApply (transactions_type_to_chain_some with "Hpost"); try assumption.
Qed.
Print Assumptions transactions_source_chain_some_region_correct.
