Require Import ZesuSsz.Automation.All.
Require Import ZesuSsz.Automation.StackArrayIndices.
Require Import isla.riscv64.riscv64.
From ZesuSsz.Proofs.WriteSuccess Require Import
  WriteSuccessExactAuthorizationsU256 WriteSuccessExactTransactionsGasLoads
  WriteSuccessExactEncoderU256 WriteSuccessExactEncoderU256Spec.
From IslaTraces.write_success_81 Require Import instrs.
Local Remove Hints IslaTraces.write_success_81.a155fc_spec.a155fc_spec_inst : typeclass_instances.
Local Remove Hints IslaTraces.write_success_81.a15600_spec.a15600_spec_inst : typeclass_instances.
Local Remove Hints IslaTraces.write_success_81.a15604_spec.a15604_spec_inst : typeclass_instances.
Local Remove Hints IslaTraces.write_success_81.a15608_spec.a15608_spec_inst : typeclass_instances.
Local Remove Hints IslaTraces.write_success_81.a15610_spec.a15610_spec_inst : typeclass_instances.

Lemma authorization_third_u256_correct `{!islaG Sigma} `{!threadG}
    sp oldra old5 bytes tail (P : iProp Sigma) :
  ([∗ list] instruction ∈ IslaTraces.write_success_81.instrs.instr_map,
    instr instruction.1 (Some instruction.2))%I -∗
  ([∗ list] instruction ∈ IslaTraces.write_success_08.instrs.instr_map,
    instr instruction.1 (Some instruction.2))%I -∗
  ([∗ list] instruction ∈ IslaTraces.write_success_01.instrs.instr_map,
    instr instruction.1 (Some instruction.2))%I -∗
  instr_body 0x155fc (authorizationU256Entry sp oldra old5 bytes 64 (BV 64 0x15614) tail P).
Proof.
  iStartProof. iIntros "#Hcaller #Hencoder #Houtput".
  iPoseProof (encoder_u256_exact_correct (transactionRowWord bytes 64 0)
    (transactionRowWord bytes 64 8) (transactionRowWord bytes 64 16)
    (transactionRowWord bytes 64 24) sp (BV 64 0x15614) tail
    (authorizationU256Frame sp bytes P) with "Hencoder Houtput") as "Hcallee".
  iEval (rewrite /IslaTraces.write_success_81.instrs.instr_map /=) in "Hcaller".
  iDestruct "Hcaller" as "#(H0 & H1 & H2 & H3 & H4 & H5 & _)".
  zesu_run. Unshelve. all: unLET.
  all: unfold transactionRowWord; zesu_normalize_stack_array_indices; reflexivity.
Qed.
Print Assumptions authorization_third_u256_correct.
