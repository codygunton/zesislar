Require Import ZesuSsz.Automation.AllLegacy.
Require Import ZesuSsz.Automation.CodeLookup.
Require Import isla.riscv64.riscv64.
From ZesuSsz.Proofs.WriteSuccess Require Import
  WriteSuccessNativeCode WriteSuccessExactTransactionsRecipientBranch
  WriteSuccessExactTransactionsRecipientBranchHandoff WriteSuccessExactTransactionsRecipientBranchAbsentHandoff
  WriteSuccessExactTransactionsRecipientPresentValueRegion WriteSuccessExactTransactionsRecipientAbsentRegion
  WriteSuccessExactTransactionsRecipientOutputToValue WriteSuccessExactTransactionsRecipientAbsentToValue
  WriteSuccessExactTransactionsValueCall.

Definition transactionRecipientValueExitFrame `{!islaG Sigma} `{!threadG}
    (sp tag first second : bv 64) (last : bv 32) (P : iProp Sigma) : iProp Sigma :=
  if bool_decide (tag = BV 64 0)
  then transactionRecipientAbsentValueSourceFrame sp first second last
    ((bv_unsigned sp + 120) ↦ₘ tag ∗ P ∗ True)
  else transactionRecipientValueSourceFrame sp first second last
    ((bv_unsigned sp + 120) ↦ₘ tag ∗ P ∗ True).
Global Instance : LithiumUnfold (@transactionRecipientValueExitFrame) := I.

Lemma transactions_recipient_value_region_correct `{!islaG Sigma} `{!threadG}
    (sp tag first second w0 w1 w2 w3 oldra old5 old11 old12 old13 olddata : bv 64)
    (last : bv 32) tail (P : iProp Sigma) :
  writeSuccessCompleteNativeCode -∗
  □ instr_pre 0x151b4 (transactionValuePost sp w0 w1 w2 w3 tail
    (transactionRecipientValueExitFrame sp tag first second last P)) -∗
  instr_body 0x15154 (transactionRecipientBranchState sp tag olddata
    (transactionRecipientBranchCallerFrame sp tag first second w0 w1 w2 w3
      oldra old5 old11 old12 old13 last tail P)).
Proof.
  iStartProof. iIntros "#Hcode #Hnext".
  iPoseProof "Hcode" as "#Hparts".
  iEval (rewrite /writeSuccessCompleteNativeCode) in "Hparts".
  iDestruct "Hparts" as "#(Hprologue & Hlookup & Hmain & Houtput & Hmemcpy & Hboolean & Hoptional & HbyteLists & Hbytes & Hint & Hu256 & Hu128)".
  iAssert ([∗ list] instruction ∈ IslaTraces.write_success_44.instrs.instr_map,
    instr instruction.1 (Some instruction.2))%I as "#Hbranch".
  { iApply instr_lookup_collect; last iExact "Hlookup".
    repeat constructor; reflexivity. }
  destruct (decide (tag = BV 64 0)) as [Htag | Htag].
  - subst tag. iEval (rewrite /transactionRecipientValueExitFrame /=) in "Hnext".
    iPoseProof (transactions_recipient_absent_region_correct with "Hcode Hnext") as "Hcallee".
    iApply (transactions_recipient_branch_correct with "Hbranch").
    + rewrite instr_pre'_eq /instr_pre'_def /=. iIntros "(_ & %Hcontra & _)". done.
    + iApply (instr_pre_wand 0x15194 0x15194 false false with "Hcallee"); [done | done |].
      iApply transactions_recipient_branch_to_absent.
  - iEval (rewrite /transactionRecipientValueExitFrame bool_decide_false //) in "Hnext".
    iPoseProof (transactions_recipient_present_value_region_correct with "Hcode Hnext") as "Hcallee".
    iApply (transactions_recipient_branch_correct with "Hbranch").
    + iApply (instr_pre_wand 0x1515c 0x1515c false false with "Hcallee"); [done | done |].
      iApply transactions_recipient_branch_to_present.
    + rewrite instr_pre'_eq /instr_pre'_def /=. iIntros "(_ & %Hcontra & _)". done.
Qed.
Print Assumptions transactions_recipient_value_region_correct.
