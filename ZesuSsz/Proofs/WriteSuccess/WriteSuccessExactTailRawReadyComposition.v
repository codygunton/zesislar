Require Import ZesuSsz.Automation.All.
Require Import isla.riscv64.riscv64.
Require Import ZesuMachineMap.Machine.
Require Import ZesuSsz.Contracts.Endpoints.
Require Import ZesuSsz.Proofs.WriteSuccess.Interfaces.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessNativeContract.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessRepresentation.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessTransactionsSpec.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessExactTransactionsLiveSpec.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessExactValueSpec.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessOutputDescriptors.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessValueBlock.
Open Scope Z_scope.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessNativeCode.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessExactTailRawReadySpec.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessExactPrefixStackFacts.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessExactTailRawLoad.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessExactTailRawLoadSpec.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessExactTailRawLoadEntryAdapter.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessExactTailRawLoadExitAdapter.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessExactTailRawCallSpec.
Lemma exact_tail_raw_ready `{!islaG Sigma} `{!threadG}
    {Decoded} `{!WriteSuccessMemoryRepresentation Decoded}
    (args : WriteSuccessArgs Decoded) (witness : writeSuccessNativeWitness Decoded)
    (P : iProp Sigma) (Hwf : writeSuccessWitnessWellFormed args witness) :
  writeSuccessCompleteNativeCode -∗
  □ instr_pre 0x15674 (exactTailRawReady args witness P) -∗
  instr_body 0x15668
    (transactionLiveLoopExit (writeSuccessFrameSp witness)
      (writeSuccessTransactionBase witness) (writeSuccessTransactions witness)
      (WriteSuccessNativeContract.writeSuccessTransactionBytes witness)
      (writeSuccessExactTailEvents witness)
      (writeSuccessExactTailCallerWithCopiedWords args witness ∗ P)).
Proof.
  have Hvalues : length (writeSuccessValues witness) = 74%nat.
  { unfold writeSuccessWitnessWellFormed in Hwf. tauto. }
  have [Hframe [Halign Hupper]] := exact_prefix_stack_facts args witness Hwf.
  have Hlower : mapRamBase defaultMap <= bv_unsigned (writeSuccessFrameSp witness).
  { change (0 <= bv_unsigned (writeSuccessFrameSp witness)).
    pose proof (bv_unsigned_in_range _ (writeSuccessFrameSp witness)). lia. }
  iIntros "#Hnative #Hnext".
  iAssert (□ instr_pre 0x15674
    (exactTailRawLoadExit (writeSuccessFrameSp witness)
      (writeSuccessValues witness) (writeSuccessExactTailEvents witness)
      (exactTailRawLoadMachineFrame args witness P)))%I with "[]" as "#HloadNext".
  { iModIntro.
    iApply (instr_pre_wand 0x15674 0x15674 true true with "Hnext");
      [done | reflexivity |].
    iIntros "Hexit".
    iApply (exact_tail_raw_load_exit_adapter with "Hexit"). }
  iPoseProof (exact_tail_raw_load (writeSuccessFrameSp witness)
    (writeSuccessValues witness) (length (writeSuccessTransactions witness))
    (writeSuccessExactTailEvents witness) (exactTailRawLoadMachineFrame args witness P)
    Hvalues Halign Hlower Hupper with "Hnative HloadNext") as "Hload".
  iApply (instr_pre_wand 0x15668 0x15668 false false with "Hload");
    [done | reflexivity |].
  iIntros "Hentry".
  iApply (exact_tail_raw_load_entry_adapter with "Hentry").
Qed.
Print Assumptions exact_tail_raw_ready.
