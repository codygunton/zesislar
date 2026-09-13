Require Import ZesuSsz.Automation.All.
Require Import ZesuSsz.Automation.StackArrayIndices.
Require Import isla.riscv64.riscv64.
From ZesuSsz.Proofs.WriteSuccess Require Import
  WriteSuccessExactAuthorizationsU256 WriteSuccessExactTransactionsGasLoads
  WriteSuccessExactEncoderU256 WriteSuccessExactEncoderU256Spec.
From IslaTraces.write_success_80 Require Import instrs.
Local Remove Hints IslaTraces.write_success_80.a155e4_spec.a155e4_spec_inst : typeclass_instances.
Local Remove Hints IslaTraces.write_success_80.a155e8_spec.a155e8_spec_inst : typeclass_instances.
Local Remove Hints IslaTraces.write_success_80.a155ec_spec.a155ec_spec_inst : typeclass_instances.
Local Remove Hints IslaTraces.write_success_80.a155f0_spec.a155f0_spec_inst : typeclass_instances.
Local Remove Hints IslaTraces.write_success_80.a155f8_spec.a155f8_spec_inst : typeclass_instances.

Lemma authorization_second_u256_correct `{!islaG Sigma} `{!threadG}
    sp oldra old5 bytes tail (P : iProp Sigma) :
  ([∗ list] instruction ∈ IslaTraces.write_success_80.instrs.instr_map,
    instr instruction.1 (Some instruction.2))%I -∗
  ([∗ list] instruction ∈ IslaTraces.write_success_08.instrs.instr_map,
    instr instruction.1 (Some instruction.2))%I -∗
  ([∗ list] instruction ∈ IslaTraces.write_success_01.instrs.instr_map,
    instr instruction.1 (Some instruction.2))%I -∗
  instr_body 0x155e4 (authorizationU256Entry sp oldra old5 bytes 32 (BV 64 0x155fc) tail P).
Proof.
  iStartProof. iIntros "#Hcaller #Hencoder #Houtput".
  iPoseProof (encoder_u256_exact_correct (transactionRowWord bytes 32 0)
    (transactionRowWord bytes 32 8) (transactionRowWord bytes 32 16)
    (transactionRowWord bytes 32 24) sp (BV 64 0x155fc) tail
    (authorizationU256Frame sp bytes P) with "Hencoder Houtput") as "Hcallee".
  iEval (rewrite /IslaTraces.write_success_80.instrs.instr_map /=) in "Hcaller".
  iDestruct "Hcaller" as "#(H0 & H1 & H2 & H3 & H4 & H5 & _)".
  zesu_run. Unshelve. all: unLET.
  all: unfold transactionRowWord; zesu_normalize_stack_array_indices; reflexivity.
Qed.
Print Assumptions authorization_second_u256_correct.
