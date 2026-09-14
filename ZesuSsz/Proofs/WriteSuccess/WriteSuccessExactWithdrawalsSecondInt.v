Require Import ZesuSsz.Automation.All.
Require Import ZesuSsz.Automation.StackArrayIndices.
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Contracts.IslarisMachine.
Require Import ZesuSsz.Export.Snapshots.
From ZesuSsz.Proofs.WriteSuccess Require Import
  WriteSuccessExactTransactionsGasLoads
  WriteSuccessExactEncoderIntFramedCall WriteSuccessObservation WriteSuccessOutputSemantic.
From IslaTraces.write_success_92 Require Import instrs.
Local Remove Hints IslaTraces.write_success_92.a156b4_spec.a156b4_spec_inst : typeclass_instances.
Local Remove Hints IslaTraces.write_success_92.a156bc_spec.a156bc_spec_inst : typeclass_instances.

Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessExactWithdrawalsInt.

Lemma withdrawal_second_int_correct `{!islaG Sigma} `{!threadG}
    sp oldra old5 old11 bytes tail (P : iProp Sigma) :
  ([∗ list] instruction ∈ IslaTraces.write_success_92.instrs.instr_map,
    instr instruction.1 (Some instruction.2))%I -∗
  ([∗ list] instruction ∈ IslaTraces.write_success_07.instrs.instr_map,
    instr instruction.1 (Some instruction.2))%I -∗
  ([∗ list] instruction ∈ IslaTraces.write_success_01.instrs.instr_map,
    instr instruction.1 (Some instruction.2))%I -∗
  instr_body 0x156b4 (withdrawalIntEntry sp oldra old5 old11 bytes 8 (BV 64 0x156c0) tail P).
Proof.
  iStartProof. iIntros "#Hcaller #Hencoder #Houtput".
  iPoseProof (encoder_int_exact_framed_correct (transactionRowWord bytes 0 8)
    sp (BV 64 0x156c0) old5 old11 tail
    (withdrawalFieldsFrame sp bytes P) with "Hencoder Houtput") as "Hcallee".
  iEval (rewrite /IslaTraces.write_success_92.instrs.instr_map /=) in "Hcaller".
  iDestruct "Hcaller" as "#(H0 & H1 & H2 & _)".
  zesu_run. Unshelve. all: unLET.
  all: unfold transactionRowWord; zesu_normalize_stack_array_indices; reflexivity.
Qed.
Print Assumptions withdrawal_second_int_correct.
