Require Import ZesuSsz.Automation.AllLegacy.
Require Import isla.riscv64.riscv64.
From ZesuSsz.Proofs.WriteSuccess Require Import
  WriteSuccessExactTransactionsDataJump WriteSuccessExactTransactionsDataToBytes WriteSuccessExactEncoderBytes.

Lemma transactions_data_bytes_call_correct `{!islaG Sigma} `{!threadG}
    data size sp oldra olddata oldsize old5 old6 old9 bytes tail (P : iProp Sigma) :
  ([∗ list] instruction ∈ IslaTraces.write_success_50.instrs.instr_map,
    instr instruction.1 (Some instruction.2))%I -∗
  ([∗ list] instruction ∈ IslaTraces.write_success_06.instrs.instr_map,
    instr instruction.1 (Some instruction.2))%I -∗
  ([∗ list] instruction ∈ IslaTraces.write_success_07.instrs.instr_map,
    instr instruction.1 (Some instruction.2))%I -∗
  ([∗ list] instruction ∈ IslaTraces.write_success_01.instrs.instr_map,
    instr instruction.1 (Some instruction.2))%I -∗
  instr_body 0x151b4 (transactionDataJumpEntry data size oldra olddata oldsize
    (transactionDataBytesFrame data size sp old5 old6 old9 bytes tail P)).
Proof.
  iStartProof. iIntros "#Hcaller #Hbytes #Hint #Houtput".
  iPoseProof (encoder_bytes_exact_correct data size sp (BV 64 0x151c4) bytes tail
    ("x22" ↦ᵣ RVal_Bits size ∗ P ∗ True)%I with "Hbytes Hint Houtput") as "Hcallee".
  iApply (transactions_data_jump_correct with "Hcaller").
  iApply (instr_pre_wand 0x15c6c 0x15c6c false false with "Hcallee"); [done | done |].
  iIntros "Hpost". iApply (transactions_data_to_bytes with "Hpost").
Qed.
Print Assumptions transactions_data_bytes_call_correct.
