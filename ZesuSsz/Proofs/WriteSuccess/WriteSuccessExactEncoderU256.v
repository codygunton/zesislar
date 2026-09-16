Require Import ZesuSsz.Automation.AllLegacy.
Require Import isla.riscv64.riscv64.
From IslaTraces.write_success_08 Require Import instrs.
From IslaTraces.write_success_01 Require Import instrs.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessExactEncoderU256Spec.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessExactEncoderU256Prefix.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessExactEncoderU256Output.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessExactEncoderU256Suffix.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessOutput.

Lemma encoder_u256_exact_correct `{!islaG Sigma} `{!threadG}
    (w0 w1 w2 w3 sp ret : bv 64) (tail : spec) (P : iProp Sigma) :
  ([∗ list] instruction ∈ IslaTraces.write_success_08.instrs.instr_map,
    instr instruction.1 (Some instruction.2))%I -∗
  ([∗ list] instruction ∈ IslaTraces.write_success_01.instrs.instr_map,
    instr instruction.1 (Some instruction.2))%I -∗
  instr_body 0x15cb0 (encoderU256ExactSpec w0 w1 w2 w3 sp ret tail P).
Proof.
  iStartProof. iIntros "#Hcode #HoutputCode".
  iAssert (□ instr_pre 0x10190 (writeOutputTraceSpec (sp - BV 64 48)%bv
    (BV 64 32) (BV 64 0x15cd8) (writeSuccessU256WordsPayload w0 w1 w2 w3) tail
    (encoderU256ExactFrame w0 w1 w2 w3 sp ret tail P)))%I as "#Houtput".
  { iModIntro. iApply instr_pre_to_body. iNext.
    iApply write_output_trace_correct. iExact "HoutputCode". }
  iEval (simpl) in "Hcode".
  iDestruct "Hcode" as
    "(#Hi0 & #Hi1 & #Hi2 & #Hi3 & #Hi4 & #Hi5 & #Hi6 & #Hi7 &
      #Hi8 & #Hi9 & #Hi10 & #Hi11 & #Hi12 & _)".
  iAssert (instr_body 0x15cd8
    (encoderU256ExactSuffixSpec w0 w1 w2 w3 sp ret tail P))%I as "Hsuffix".
  { iApply encoder_u256_exact_suffix_correct.
    simpl. iFrame "Hi10 Hi11 Hi12". }
  iApply encoder_u256_exact_prefix_correct.
  { simpl. iFrame "Hi0 Hi1 Hi2 Hi3 Hi4 Hi5". }
  iAssert (instr_body 0x15cc8
    (encoderU256ExactAtOutputSpec w0 w1 w2 w3 sp ret tail P))%I as "Hcall".
  { iApply (encoder_u256_exact_output_correct with "[ ] Houtput Hsuffix").
    simpl. iFrame "Hi6 Hi7 Hi8 Hi9". }
  iApply (instr_pre_wand 0x15cc8 0x15cc8 false false with "Hcall");
    [done | done |].
  iApply encoder_u256_exact_words_to_payload.
Qed.

Lemma encoder_u256_exact_pre `{!islaG Sigma} `{!threadG}
    (w0 w1 w2 w3 sp ret : bv 64) (tail : spec) (P : iProp Sigma) :
  ([∗ list] instruction ∈ IslaTraces.write_success_08.instrs.instr_map,
    instr instruction.1 (Some instruction.2))%I -∗
  ([∗ list] instruction ∈ IslaTraces.write_success_01.instrs.instr_map,
    instr instruction.1 (Some instruction.2))%I -∗
  □ instr_pre 0x15cb0 (encoderU256ExactSpec w0 w1 w2 w3 sp ret tail P).
Proof.
  iStartProof. iIntros "#Hcode #Houtput". iModIntro.
  iApply instr_pre_to_body. iNext.
  iApply encoder_u256_exact_correct; iAssumption.
Qed.

Print Assumptions encoder_u256_exact_correct.
Print Assumptions encoder_u256_exact_pre.
