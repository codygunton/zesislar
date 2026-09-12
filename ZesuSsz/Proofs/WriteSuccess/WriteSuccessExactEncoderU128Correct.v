Require Import ZesuSsz.Automation.All.
Require Import isla.riscv64.riscv64.
From IslaTraces.write_success_127 Require Import instrs.
From IslaTraces.write_success_01 Require Import instrs.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessExactEncoderU128.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessExactEncoderU128Prefix.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessExactEncoderU128Output.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessOutput.

Lemma encoder_u128_exact_correct `{!islaG Sigma} `{!threadG}
    (low high sp ret : bv 64) (tail : spec) (P : iProp Sigma) :
  ([∗ list] instruction ∈ IslaTraces.write_success_127.instrs.instr_map,
    instr instruction.1 (Some instruction.2))%I -∗
  ([∗ list] instruction ∈ IslaTraces.write_success_01.instrs.instr_map,
    instr instruction.1 (Some instruction.2))%I -∗
  instr_body 0x15ce4 (encoderU128ExactSpec low high sp ret tail P).
Proof.
  iStartProof. iIntros "#Hcode #HoutputCode".
  iAssert (instr_body 0x15d04
    (encoderU128ExactSuffixSpec low high sp ret tail P))%I as "Hsuffix".
  { iApply encoder_u128_exact_suffix_correct. iExact "Hcode". }
  iAssert (□ instr_pre 0x10190 (writeOutputTraceSpec (sp - BV 64 32)%bv
    (BV 64 16) (BV 64 0x15d04) (writeSuccessU128WordsPayload low high) tail
    (encoderU128ExactFrame low high sp ret tail P)))%I as "#Houtput".
  { iModIntro. iApply instr_pre_to_body. iNext.
    iApply write_output_trace_correct. iExact "HoutputCode". }
  iEval (simpl) in "Hcode".
  iDestruct "Hcode" as
    "(#Hi0 & #Hi1 & #Hi2 & #Hi3 & #Hi4 & #Hi5 & #Hi6 & #Hi7 & _)".
  iApply encoder_u128_exact_prefix_correct.
  { simpl. iFrame "Hi0 Hi1 Hi2 Hi3". }
  iAssert (instr_body 0x15cf4
    (encoderU128ExactAtOutputSpec low high sp ret tail P))%I as "Hcall".
  { iApply (encoder_u128_exact_output_correct with "[ ] Houtput Hsuffix").
    simpl. iFrame "Hi4 Hi5 Hi6 Hi7". }
  iApply (instr_pre_wand 0x15cf4 0x15cf4 false false with "Hcall");
    [done | done |].
  iApply encoder_u128_exact_words_to_payload.
Qed.

Lemma encoder_u128_exact_pre `{!islaG Sigma} `{!threadG}
    (low high sp ret : bv 64) (tail : spec) (P : iProp Sigma) :
  ([∗ list] instruction ∈ IslaTraces.write_success_127.instrs.instr_map,
    instr instruction.1 (Some instruction.2))%I -∗
  ([∗ list] instruction ∈ IslaTraces.write_success_01.instrs.instr_map,
    instr instruction.1 (Some instruction.2))%I -∗
  □ instr_pre 0x15ce4 (encoderU128ExactSpec low high sp ret tail P).
Proof.
  iStartProof. iIntros "#Hcode #Houtput". iModIntro.
  iApply instr_pre_to_body. iNext.
  iApply encoder_u128_exact_correct; iAssumption.
Qed.

Print Assumptions encoder_u128_exact_correct.
Print Assumptions encoder_u128_exact_pre.
