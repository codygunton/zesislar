Require Import ZesuSsz.Automation.All.
Require Import ZesuMachineMap.Machine.
Require Import isla.riscv64.riscv64.
From ZesuSsz.Proofs.WriteSuccess Require Import
  WriteSuccessExactAuthorizationsInitial WriteSuccessExactAuthorizationsLoopSpec
  WriteSuccessExactAuthorizationsCountInitial WriteSuccessExactAuthorizationsPublic
  WriteSuccessExactAuthorizationsCount WriteSuccessExactTransactionsMaxBlobFeeCount.

Lemma authorization_count_continuation_closed `{!islaG Sigma} `{!threadG}
    (sp low high : bv 64) base row rest source tail (P : iProp Sigma) :
  ([∗ list] instruction ∈ IslaTraces.write_success_74.instrs.instr_map,
    instr instruction.1 (Some instruction.2))%I -∗
  authorizationLoopCode -∗
  □ instr_pre 0x15584 (authorizationCountPost sp (Z_to_bv 64 (Z.of_nat (S (length rest))))
    (WriteSuccessExactAuthorizationsModel.writeSuccessExactAuthorizationEvents sp (row :: rest) tail)
    (maxBlobFeeCountFrame sp low high (authorizationInitialCaller sp low high base row rest source tail P))).
Proof.
  iStartProof. iIntros "#H74 #Hloop". iModIntro.
  rewrite instr_pre'_eq. iNext. iIntros "Hpost".
  iPoseProof (authorization_count_to_initial with "Hpost") as "Hinitial".
  iDestruct "Hinitial" as "(%Hfacts & Hinitial & _)".
  iPoseProof (authorization_initial_closed sp (BV 64 0x15584) (BV 64 (mapIoContextAddress defaultMap))
    base row rest source tail (authorizationFeeFrame sp low high rest P) Hfacts
    with "H74 Hloop") as "Hbody".
  iEval (rewrite instr_pre'_eq) in "Hbody".
  iApply ("Hbody" with "Hinitial").
Qed.
Print Assumptions authorization_count_continuation_closed.
