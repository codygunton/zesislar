Require Import ZesuSsz.Automation.All.
Require Import isla.riscv64.riscv64.
From ZesuSsz.Proofs.WriteSuccess Require Import
  WriteSuccessExactWithdrawalsInt WriteSuccessExactWithdrawalsSecondInt WriteSuccessExactWithdrawalsThirdInt
  WriteSuccessExactWithdrawalsIntNext WriteSuccessExactWithdrawalsAddressEntry
  WriteSuccessExactWithdrawalsOutputWhole WriteSuccessExactWithdrawalsPhases.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessExactWithdrawalsAmountSuffix.
Lemma withdrawal_address_suffix_correct `{!islaG Sigma} `{!threadG}
    sp bytes tail (P : iProp Sigma) :
  length bytes = 48%nat ->
  ([∗ list] instruction ∈ IslaTraces.write_success_93.instrs.instr_map,
    instr instruction.1 (Some instruction.2))%I -∗
  ([∗ list] instruction ∈ IslaTraces.write_success_94.instrs.instr_map,
    instr instruction.1 (Some instruction.2))%I -∗
  ([∗ list] instruction ∈ IslaTraces.write_success_07.instrs.instr_map,
    instr instruction.1 (Some instruction.2))%I -∗
  ([∗ list] instruction ∈ IslaTraces.write_success_01.instrs.instr_map,
    instr instruction.1 (Some instruction.2))%I -∗
  instr_body 0x156dc (withdrawalIntPost sp bytes (BV 64 0x156dc) tail ("x18" ↦ᵣ RVal_Bits (sp + BV 64 1768)%bv ∗ P ∗ True)%I) -∗
  instr_body 0x156c0 (withdrawalIntPost sp bytes (BV 64 0x156c0)
    (withdrawalExactPhaseEvents 2 sp bytes tail) ("x18" ↦ᵣ RVal_Bits (sp + BV 64 1768)%bv ∗ P ∗ True)%I).
Proof.
  intros Hlen. iStartProof. iIntros "#Haddress #Hamount #Hint #Houtput Hfinal".
  iPoseProof (withdrawal_amount_suffix_correct sp bytes tail P Hlen
    with "Hamount Hint Houtput Hfinal") as "Hlast".
  iPoseProof (withdrawal_whole_output_correct sp (BV 64 0x156c0) (BV 64 0x2401a0b8)
    (sp - BV 64 16)%bv (BV 64 8) bytes (withdrawalExactPhaseEvents 3 sp bytes tail)
    (withdrawalAddressCallerFrame sp P) with "Haddress Houtput Hlast") as "Hcallee".
  iApply (instr_pre_wand 0x156c0 0x156c0 false false with "Hcallee"); [done | done |].
  iIntros "Hpost". iEval (rewrite withdrawal_phase_2) in "Hpost".
  iApply (withdrawal_int_to_address_entry with "Hpost").
Qed.
Print Assumptions withdrawal_address_suffix_correct.
