Require Import ZesuSsz.Automation.All.
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Contracts.Endpoints.
Require Import ZesuSsz.Contracts.DecodeHeap.
Require Import ZesuSsz.Contracts.DecodeMachine.
Require Import ZesuSsz.Proofs.Main.PrefixResources.
Require Import ZesuSsz.Proofs.Main.Prefix.
Require Import ZesuSsz.Proofs.Main.DecodeEntry.
Definition mainToDecodeEntryResources `{!islaG Sigma} `{!threadG}
    (decodeTail successExitTail : DecodeBoundaryArgs -> spec)
    (a0 a1 oldSaved oldSize oldInput x5 x6 x12 x13 : bv 64) :
    IslarisContractResources DecodeBoundaryArgs unit := {|
  islarisCode := (islarisCode _ _
      (mainPrefixResources decodeTail successExitTail
        a0 a1 oldSaved oldSize oldInput x5 x6 x12 x13) ∗
    islarisCode _ _
      (mainBeforeDecodeCallResources decodeTail successExitTail (BV 64 0x14ccc)
        (BV 64 mainAllocatorStateAddress) (BV 64 mainAllocatorVtableAddress)))%I;
  islarisEntry := islarisEntry _ _
    (mainPrefixResources decodeTail successExitTail
      a0 a1 oldSaved oldSize oldInput x5 x6 x12 x13);
  islarisExit := fun args _ =>
    islarisEntry _ _ (mainDecodeConcreteResources decodeTail successExitTail) args
|}.
Theorem main_to_decode_entry_state_correct `{!islaG Sigma} `{!threadG}
    (decodeTail successExitTail : DecodeBoundaryArgs -> spec)
    (a0 a1 oldSaved oldSize oldInput x5 x6 x12 x13 : bv 64) :
  ⊢ IslarisContractSpec 0x14cb0 0x12168 (fun _ _ => True%type)
    (mainToDecodeEntryResources decodeTail successExitTail
      a0 a1 oldSaved oldSize oldInput x5 x6 x12 x13).
Proof.
  rewrite /IslarisContractSpec /mainToDecodeEntryResources /=.
  iIntros "(HprefixCode&HcallCode)" (args).
  iPoseProof (main_prefix_state_correct decodeTail successExitTail
    a0 a1 oldSaved oldSize oldInput x5 x6 x12 x13 with "HprefixCode") as "Hprefix".
  iSpecialize ("Hprefix" $! args).
  iEval (rewrite instr_pre'_eq /instr_pre'_def /=) in "Hprefix".
  rewrite instr_pre'_eq /instr_pre'_def /=.
  iIntros "[Hentry Hreturn]". iApply "Hprefix". iFrame "Hentry".
  iNext. iIntros "Hexit". iDestruct "Hexit" as (outcome) "[_ Hexit]".
  iPoseProof (main_before_decode_call_state_correct decodeTail successExitTail
    (BV 64 0x14ccc) (BV 64 mainAllocatorStateAddress) (BV 64 mainAllocatorVtableAddress)
    with "HcallCode") as "Hcall".
  iSpecialize ("Hcall" $! args).
  iEval (rewrite instr_pre'_eq /instr_pre'_def /=) in "Hcall".
  iApply "Hcall". iFrame "Hexit Hreturn".
Qed.
Print Assumptions main_to_decode_entry_state_correct.
