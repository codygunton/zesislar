Require Import ZesuSsz.Automation.All.
Require Import isla.riscv64.riscv64.
From ZesuSsz.Proofs.WriteSuccess Require Import
  WriteSuccessExactWithdrawalsInt WriteSuccessExactWithdrawalsSecondInt WriteSuccessExactWithdrawalsThirdInt
  WriteSuccessExactWithdrawalsIntNext WriteSuccessExactWithdrawalsAddressEntry
  WriteSuccessExactWithdrawalsOutputWhole WriteSuccessExactWithdrawalsPhases.
Lemma withdrawal_amount_suffix_correct `{!islaG Sigma} `{!threadG}
    sp bytes tail (P : iProp Sigma) :
  length bytes = 48%nat ->
  ([∗ list] instruction ∈ IslaTraces.write_success_94.instrs.instr_map,
    instr instruction.1 (Some instruction.2))%I -∗
  ([∗ list] instruction ∈ IslaTraces.write_success_07.instrs.instr_map,
    instr instruction.1 (Some instruction.2))%I -∗
  ([∗ list] instruction ∈ IslaTraces.write_success_01.instrs.instr_map,
    instr instruction.1 (Some instruction.2))%I -∗
  instr_body 0x156dc (withdrawalIntPost sp bytes (BV 64 0x156dc) tail ("x18" ↦ᵣ RVal_Bits (sp + BV 64 1768)%bv ∗ P ∗ True)%I) -∗
  instr_body 0x156d0 (withdrawalWholeOutputPost sp bytes
    (withdrawalExactPhaseEvents 3 sp bytes tail) (withdrawalAddressCallerFrame sp P)).
Proof.
  intros Hlen. iStartProof. iIntros "#Hamount #Hint #Houtput Hfinal".
  iAssert (instr_pre 0x156dc (withdrawalIntPost sp bytes (BV 64 0x156dc) tail ("x18" ↦ᵣ RVal_Bits (sp + BV 64 1768)%bv ∗ P ∗ True)%I)) with "[Hfinal]" as "Hnext".
  { iApply (instr_pre_wand 0x156dc 0x156dc false true with "Hfinal"); [done | done |]. iIntros "$". }
  iPoseProof (withdrawal_third_int_correct sp (BV 64 0x156d0) (BV 64 0x2401a0b8)
    (BV 64 20) bytes tail ("x18" ↦ᵣ RVal_Bits (sp + BV 64 1768)%bv ∗ P ∗ True)%I with "Hamount Hint Houtput") as "Hcallee".
  iApply (instr_pre_wand 0x156d0 0x156d0 false false with "Hcallee"); [done | done |].
  iIntros "Hpost". iEval (rewrite (withdrawal_phase_3 sp bytes tail Hlen)) in "Hpost".
  iApply (withdrawal_address_to_int_entry sp bytes tail P Hlen with "Hpost Hnext").
Qed.
Print Assumptions withdrawal_amount_suffix_correct.
