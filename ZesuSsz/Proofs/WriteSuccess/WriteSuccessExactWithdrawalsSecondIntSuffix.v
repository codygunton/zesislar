Require Import ZesuSsz.Automation.AllLegacy.
Require Import ZesuMachineMap.Machine.
Require Import isla.riscv64.riscv64.
From ZesuSsz.Proofs.WriteSuccess Require Import
  WriteSuccessExactWithdrawalsInt WriteSuccessExactWithdrawalsSecondInt WriteSuccessExactWithdrawalsThirdInt
  WriteSuccessExactWithdrawalsIntNext WriteSuccessExactWithdrawalsAddressEntry
  WriteSuccessExactWithdrawalsOutputWhole WriteSuccessExactWithdrawalsPhases.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessExactWithdrawalsAddressSuffix.
Lemma withdrawal_second_int_suffix_correct `{!islaG Sigma} `{!threadG}
    sp bytes tail (P : iProp Sigma) :
  length bytes = 48%nat ->
  ([∗ list] instruction ∈ IslaTraces.write_success_92.instrs.instr_map,
    instr instruction.1 (Some instruction.2))%I -∗
  ([∗ list] instruction ∈ IslaTraces.write_success_93.instrs.instr_map,
    instr instruction.1 (Some instruction.2))%I -∗
  ([∗ list] instruction ∈ IslaTraces.write_success_94.instrs.instr_map,
    instr instruction.1 (Some instruction.2))%I -∗
  ([∗ list] instruction ∈ IslaTraces.write_success_07.instrs.instr_map,
    instr instruction.1 (Some instruction.2))%I -∗
  ([∗ list] instruction ∈ IslaTraces.write_success_01.instrs.instr_map,
    instr instruction.1 (Some instruction.2))%I -∗
  instr_body 0x156dc (withdrawalIntPost sp bytes (BV 64 0x156dc) tail ("x18" ↦ᵣ RVal_Bits (sp + BV 64 1768)%bv ∗ P ∗ True)%I) -∗
  instr_body 0x156b4 (withdrawalIntPost sp bytes (BV 64 0x156b4)
    (withdrawalExactPhaseEvents 1 sp bytes tail) ("x18" ↦ᵣ RVal_Bits (sp + BV 64 1768)%bv ∗ P ∗ True)%I).
Proof.
  intros Hlen. iStartProof. iIntros "#Hsecond #Haddress #Hamount #Hint #Houtput Hfinal".
  iPoseProof (withdrawal_address_suffix_correct sp bytes tail P Hlen
    with "Haddress Hamount Hint Houtput Hfinal") as "Hlast".
  iAssert (instr_pre 0x156c0 (withdrawalIntPost sp bytes (BV 64 0x156c0)
    (withdrawalExactPhaseEvents 2 sp bytes tail) ("x18" ↦ᵣ RVal_Bits (sp + BV 64 1768)%bv ∗ P ∗ True)%I)) with "[Hlast]" as "Hnext".
  { iApply (instr_pre_wand 0x156c0 0x156c0 false true with "Hlast"); [done | done |]. iIntros "$". }
  iPoseProof (withdrawal_second_int_correct sp (BV 64 0x156b4) (BV 64 (mapIoContextAddress defaultMap))
    (BV 64 8) bytes (withdrawalExactPhaseEvents 2 sp bytes tail) ("x18" ↦ᵣ RVal_Bits (sp + BV 64 1768)%bv ∗ P ∗ True)%I
    with "Hsecond Hint Houtput") as "Hcallee".
  iApply (instr_pre_wand 0x156b4 0x156b4 false false with "Hcallee"); [done | done |].
  iIntros "Hpost". iEval (rewrite (withdrawal_phase_1 sp bytes tail Hlen)) in "Hpost".
  iApply (withdrawal_int_next_entry sp bytes (BV 64 0x156b4) (BV 64 0x156c0) 8
    (withdrawalExactPhaseEvents 2 sp bytes tail)
    ("x18" ↦ᵣ RVal_Bits (sp + BV 64 1768)%bv ∗ P ∗ True)%I with "Hpost Hnext").
Qed.
Print Assumptions withdrawal_second_int_suffix_correct.
