Require Import ZesuSsz.Automation.All.
Require Import isla.riscv64.riscv64.
From IslaTraces.write_success_blocks Require Import Index.
From IslaTraces.write_success_88 Require Import instrs.
Require Import ZesuSsz.Contracts.IslarisCode.
Require Import ZesuSsz.Contracts.Endpoints.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessNativeCode.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessNativeContract.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessRepresentation.
Require Import ZesuSsz.Proofs.WriteSuccess.Interfaces.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessExactPostTransactionsWithdrawalLoad.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessExactTailRawCallReturnSpec.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessExactTailWithdrawalLoadSpec.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessExactTailWithdrawalLoadEntryAdapter.
Open Scope Z_scope.

Lemma exact_tail_withdrawal_load_code `{!islaG Sigma} `{!threadG} :
  instr_lookup_resources IslaTraces.write_success_blocks.Index.lookup -∗
  ([∗ list] instruction ∈ take 4 IslaTraces.write_success_88.instrs.instr_map,
    instr instruction.1 (Some instruction.2))%I.
Proof.
  iStartProof. iIntros "#Hlookup".
  iEval (rewrite /instr_lookup_resources) in "Hlookup".
  iPoseProof ("Hlookup" $! 0x15678 with "[]") as "#H15678".
  { iPureIntro. rewrite IslaTraces.write_success_blocks.Index.lookup_a15678. done. }
  iPoseProof ("Hlookup" $! 0x1567c with "[]") as "#H1567c".
  { iPureIntro. rewrite IslaTraces.write_success_blocks.Index.lookup_a1567c. done. }
  iPoseProof ("Hlookup" $! 0x15680 with "[]") as "#H15680".
  { iPureIntro. rewrite IslaTraces.write_success_blocks.Index.lookup_a15680. done. }
  iPoseProof ("Hlookup" $! 0x15684 with "[]") as "#H15684".
  { iPureIntro. rewrite IslaTraces.write_success_blocks.Index.lookup_a15684. done. }
  iEval (rewrite IslaTraces.write_success_blocks.Index.lookup_a15678) in "H15678".
  iEval (rewrite IslaTraces.write_success_blocks.Index.lookup_a1567c) in "H1567c".
  iEval (rewrite IslaTraces.write_success_blocks.Index.lookup_a15680) in "H15680".
  iEval (rewrite IslaTraces.write_success_blocks.Index.lookup_a15684) in "H15684".
  cbn.
  iSplitL "H15678"; first iExact "H15678".
  iSplitL "H1567c"; first iExact "H1567c".
  iSplitL "H15680"; first iExact "H15680".
  iSplitL "H15684"; first iExact "H15684". done.
Qed.
Print Assumptions exact_tail_withdrawal_load_code.

Lemma exact_tail_raw_return_through_withdrawal_load
    `{!islaG Sigma} `{!threadG}
    {Decoded} `{!WriteSuccessMemoryRepresentation Decoded}
    (args : WriteSuccessArgs Decoded) (witness : writeSuccessNativeWitness Decoded)
    (P : iProp Sigma) :
  writeSuccessCompleteNativeCode -∗
  instr_body 0x15688 (exactTailWithdrawalLoadPost args witness P) -∗
  instr_body 0x15678 (exactTailRawCallReturn args witness P).
Proof.
  iStartProof. iIntros "#Hnative Hnext".
  iPoseProof (write_success_native_main_code with "Hnative") as "#Hmain".
  iEval (rewrite /writeSuccessNativeMainCode) in "Hmain".
  iDestruct "Hmain" as "(#Hlookup & #Hspec & _)".
  iPoseProof (exact_tail_withdrawal_load_code with "Hlookup") as "#Hcode".
  rewrite instr_pre'_eq.
  iEval (rewrite -instr_pre'_eq) in "Hnext".
  iIntros "Hreturn".
  iPoseProof (exact_tail_raw_return_to_withdrawal_load with "Hreturn") as "Hentry".
  iEval (rewrite /exactTailWithdrawalLoadEntry) in "Hentry".
  iDestruct "Hentry" as (oldra old8 old9 olddata) "Hentry".
  iPoseProof (post_transactions_exact_withdrawal_load_correct
    (writeSuccessFrameSp witness) oldra old8 old9 olddata
    (take 69 (writeSuccessValues witness))
    (exactTailWithdrawalLoadFrame args witness P)
    with "Hcode Hnext") as "Hbody".
  iEval (rewrite instr_pre'_eq) in "Hbody".
  iApply ("Hbody" with "Hentry").
Qed.
Print Assumptions exact_tail_raw_return_through_withdrawal_load.
