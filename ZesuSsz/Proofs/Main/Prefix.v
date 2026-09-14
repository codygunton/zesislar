Require Import ZesuSsz.Automation.All.
Require Import isla.riscv64.riscv64.
Require Import ZesuMachineMap.Machine.
Require Import ZesuSsz.Contracts.Endpoints.
Require Import ZesuSsz.Contracts.DecodeHeap.
Require Import ZesuSsz.Contracts.DecodeMachine.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessPrologueSpec.
Require Import ZesuSsz.Proofs.Main.Resources.
Require Import ZesuSsz.Proofs.Main.DecodeEntry.
Require Import ZesuSsz.Proofs.Main.AllocatorAdapter.
Require Import ZesuSsz.Proofs.Main.PrefixResources.
Require Import ZesuSsz.Proofs.ReadInput.ReadInput.
Require Import ZesuSsz.Proofs.Main.PrefixArithmetic.
Require Import ZesuSsz.Proofs.Main.Prologue.
Require Import ZesuSsz.Proofs.Main.PrefixReadInput.
Require Import ZesuSsz.Proofs.Main.PrefixEntryBridge.
Theorem main_prefix_state_correct `{!islaG Sigma} `{!threadG}
    (decodeTail successExitTail : DecodeBoundaryArgs -> spec)
    (a0 a1 oldSaved oldSize oldInput x5 x6 x12 x13 : bv 64) :
  ⊢ IslarisContractSpec 0x14cb0 0x14cec (fun _ _ => True%type)
    (mainPrefixResources decodeTail successExitTail
      a0 a1 oldSaved oldSize oldInput x5 x6 x12 x13).
Proof.
  rewrite /IslarisContractSpec /mainPrefixResources /=.
  iIntros "(HprologueCode&HreadCode&HallocCode)" (args).
  rewrite instr_pre'_eq /instr_pre'_def /=.
  iIntros "[(Hentry&Hframe&_) Hreturn]".
  set P := (mainPrefixFrame decodeTail args oldInput x5 x6 x12 x13 ∗
    instr_pre 0x14cec (∃ outcome : unit, ⌜True%type⌝ ∗
      islarisEntry _ _
        (mainBeforeDecodeCallResources decodeTail successExitTail (BV 64 0x14ccc)
          (BV 64 mainAllocatorStateAddress) (BV 64 mainAllocatorVtableAddress)) args))%I.
  iAssert (instr_body 0x10140
    (mainReadInputCall (mainPrefixInitialSp args)
      (Z_to_bv 64 (decodeSavedReturnAddress args)) ∗ P ∗ True))
    with "[HreadCode HallocCode]" as "Hread".
  { rewrite /P instr_pre'_eq /instr_pre'_def /=.
    iIntros "(Hcall&(Hframe&Hreturn)&_)".
    iPoseProof (main_prologue_exit_read_entry decodeTail args oldInput x5 x6 x12 x13
      with "[$Hcall $Hframe]") as "HreadEntry".
    iPoseProof (main_read_input_prefix_state_correct decodeTail successExitTail x12 x13
      with "HallocCode HreadCode") as "Hread".
    iSpecialize ("Hread" $! args).
    iEval (rewrite instr_pre'_eq /instr_pre'_def /=) in "Hread".
    iApply "Hread". iFrame "HreadEntry Hreturn". }
  iPoseProof (main_prologue_correct_with_frame
    (mainPrefixInitialSp args) (Z_to_bv 64 (decodeSavedReturnAddress args))
    a0 a1 oldSaved oldSize P with "HprologueCode Hread") as "Hprologue".
  iEval (rewrite instr_pre'_eq /instr_pre'_def /=) in "Hprologue".
  iApply "Hprologue". rewrite /P instr_pre'_eq /instr_pre'_def /=. iFrame.
Qed.
Print Assumptions main_prefix_state_correct.
