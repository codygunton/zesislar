Require Import ZesuSsz.Automation.All.
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessExactEncoderU256.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessExactEncoderU256Spec.

Definition encoderU256ExactFramedCallSpec `{!islaG Sigma} `{!threadG} : iProp Sigma :=
  (∃ (w0 w1 w2 w3 sp ret : bv 64) (tail : spec) (P : iProp Sigma),
    encoderU256ExactSpec w0 w1 w2 w3 sp ret tail P ∗ True)%I.
Global Instance : LithiumUnfold (@encoderU256ExactFramedCallSpec) := I.

Lemma encoder_u256_exact_framed_call_pre `{!islaG Sigma} `{!threadG} :
  ([∗ list] instruction ∈ IslaTraces.write_success_08.instrs.instr_map,
    instr instruction.1 (Some instruction.2))%I -∗
  ([∗ list] instruction ∈ IslaTraces.write_success_01.instrs.instr_map,
    instr instruction.1 (Some instruction.2))%I -∗
  □ instr_pre 0x15cb0 encoderU256ExactFramedCallSpec.
Proof.
  iStartProof. iIntros "#Hencoder #Houtput". iModIntro.
  iApply instr_pre_to_body. iNext. rewrite instr_pre'_eq.
  iIntros "Hentry". iDestruct "Hentry" as (w0 w1 w2 w3 sp ret tail P) "[Hentry _]".
  iPoseProof (encoder_u256_exact_correct w0 w1 w2 w3 sp ret tail P
    with "Hencoder Houtput") as "Hbody".
  iEval (rewrite instr_pre'_eq) in "Hbody". iApply ("Hbody" with "Hentry").
Qed.
Print Assumptions encoder_u256_exact_framed_call_pre.
