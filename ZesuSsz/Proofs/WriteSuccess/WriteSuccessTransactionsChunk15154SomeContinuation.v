From Coq Require Import Lists.List ZArith.ZArith.
Require Import isla.riscv64.riscv64.
From IslaTraces.write_success_blocks Require Import Index HintsTransactionsLoop.
Require Import ZesuSsz.Contracts.IslarisCode.
Require Import ZesuSsz.Contracts.IslarisMachine.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessCalls.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessEncoderBooleanCall.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessTransactionsBoundary1519c.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessTransactionsOptionalAddressSome.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessTransactionsOptionalAddressSome15180To1518c.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessTransactionsOptionalAddressSome1518cTo15190.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessTransactionsOptionalAddressSome15190.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessTransactionsOptionalAddressSomeHandoff.

Lemma write_success_transactions_chunk_15168_to_1519c
    `{!islaG Sigma} `{!threadG} (P : iProp Sigma) :
  instr_lookup_resources IslaTraces.write_success_blocks.Index.lookup -∗
  IslaTraces.write_success_blocks.Index.spec_instr_resources -∗
  □ instr_pre 0x15b9c zesuEncoderBooleanCallSpec -∗
  □ instr_pre 0x10190 zesuWriteOutputCallSpec -∗
  instr_body 0x1519c (writeSuccessTransactionsAt1519cSpec P) -∗
  instr_body 0x15168
    (writeSuccessTransactionsOptionalAddressSomeAt15168Spec P).
Proof.
  move => *. iStartProof.
  iIntros "_ #Hlookup #Hcode #Hboolean #Houtput Hnext".
  iPoseProof (write_success_transactions_optional_address_some_15190 P
    with "Hlookup Hcode Hnext") as "H15190".
  iPoseProof (write_success_transactions_optional_address_some_1518c_to_15190 P
    with "Hlookup Hcode Houtput H15190") as "H1518c".
  iPoseProof (write_success_transactions_optional_address_some_15180_to_1518c P
    with "Hlookup Hcode H1518c") as "H15180".
  iApply (write_success_transactions_optional_address_some P
    with "Hlookup Hcode Hboolean H15180").
Qed.
