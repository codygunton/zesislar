Require Import ZesuSsz.Automation.All.
Require Import ZesuSsz.Automation.StackArrayIndices.
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Contracts.IslarisMachine.
Require Import ZesuSsz.Export.Snapshots.
From ZesuSsz.Proofs.WriteSuccess Require Import
  WriteSuccessExactAuthorizationsU256 WriteSuccessExactTransactionsGasLoads
  WriteSuccessExactEncoderIntFramedCall WriteSuccessObservation WriteSuccessOutputSemantic.
From IslaTraces.write_success_79 Require Import instrs.
Local Remove Hints IslaTraces.write_success_79.a155d8_spec.a155d8_spec_inst : typeclass_instances.
Local Remove Hints IslaTraces.write_success_79.a155e0_spec.a155e0_spec_inst : typeclass_instances.

Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessExactAuthorizationsInt.

Lemma authorization_second_int_correct `{!islaG Sigma} `{!threadG}
    sp oldra old5 old11 bytes tail (P : iProp Sigma) :
  ([∗ list] instruction ∈ IslaTraces.write_success_79.instrs.instr_map,
    instr instruction.1 (Some instruction.2))%I -∗
  ([∗ list] instruction ∈ IslaTraces.write_success_07.instrs.instr_map,
    instr instruction.1 (Some instruction.2))%I -∗
  ([∗ list] instruction ∈ IslaTraces.write_success_01.instrs.instr_map,
    instr instruction.1 (Some instruction.2))%I -∗
  instr_body 0x155d8 (authorizationIntEntry sp oldra old5 old11 bytes 104 (BV 64 0x155e4) tail P).
Proof.
  iStartProof. iIntros "#Hcaller #Hencoder #Houtput".
  iPoseProof (encoder_int_exact_framed_correct (transactionRowWord bytes 0 104)
    sp (BV 64 0x155e4) old5 old11 tail
    (authorizationU256Frame sp bytes P) with "Hencoder Houtput") as "Hcallee".
  iEval (rewrite /IslaTraces.write_success_79.instrs.instr_map /=) in "Hcaller".
  iDestruct "Hcaller" as "#(H0 & H1 & H2 & _)".
  zesu_run. Unshelve. all: unLET.
  all: unfold transactionRowWord; zesu_normalize_stack_array_indices; reflexivity.
Qed.
Print Assumptions authorization_second_int_correct.
