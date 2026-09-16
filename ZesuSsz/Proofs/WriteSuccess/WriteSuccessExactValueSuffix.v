Require Import ZesuSsz.Automation.AllLegacy.
From Coq Require Import Lists.List ZArith.ZArith.
Require Import isla.riscv64.riscv64.
From IslaTraces.write_success_blocks Require Import Index HintsValueBlock.
Require Import ZesuSsz.Contracts.IslarisCode.
Require Import ZesuSsz.Contracts.IslarisMachine.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessExactEncoderIntCall.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessExactValueSpec.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessPayloadCall.

Local Remove Hints subsume_instr_pre'_inst : typeclass_instances.
Local Existing Instance subsume_instr_pre_wand_inst | 1.

#[local] Hint Rewrite Z_to_bv_add Z_to_bv_unsigned :
  lithium_rewrite isla_coq_rewrite.

#[local] Hint Extern 7
  (FindInContext (FindInstrKind ?address ?later) FICSyntactic) =>
  let reduced := eval vm_compute in address in
  first [ constr_eq address reduced; fail 1
        | change (FindInContext (FindInstrKind reduced later) FICSyntactic);
          typeclasses eauto ] : typeclass_instances.

Lemma write_success_exact_value_suffix `{!islaG Sigma} `{!threadG}
    (sp : bv 64) (values : list (bv 64)) (payload : list (bv 8))
    (tail : spec) (P : iProp Sigma) :
  instr_lookup_resources IslaTraces.write_success_blocks.Index.lookup -∗
  IslaTraces.write_success_blocks.Index.spec_instr_resources -∗
  □ instr_pre 0x10190 zesuWriteOutputPayloadCallSpec -∗
  □ instr_pre 0x15d10 zesuEncoderIntPayloadCallSpec -∗
  instr_body 0x14ed4
    (writeSuccessExactValueBaseFeeReturnSpec sp values payload tail P).
Proof.
  move => *. iStartProof.
  iIntros "_ #Hlookup #Hcode #Houtput #Hint".
  iEval (unfold IslaTraces.write_success_blocks.Index.spec_instr_resources)
    in "Hcode".
  liARun.
  Unshelve. all: try prepare_sidecond; try assumption;
    try (rewrite length_take; lia); try bv_solve; try lia; try iFrame.
  Unshelve.
  all: try (iExists (writeSuccessExactValueIntEvent sp values 8 tail, tt)ₗ;
    repeat iSplit; try iPureIntro; try assumption;
    try (replace (bv_unsigned LET0) with (bv_unsigned (sp + 1588)%bv)
      by bv_solve; reflexivity);
    try (rewrite writeSuccessValueBlockHash_length; [reflexivity | assumption]);
    try bv_solve; try lia; try iFrame).
  Unshelve.
  all: try (iApply instr_pre_to_body; iNext; liARun).
  Unshelve. all: try prepare_sidecond; try assumption;
    try (rewrite length_take; lia); try bv_solve; try lia; try iFrame.
  Unshelve.
  all: try iExists (tail, tt)ₗ.
  all: try (iSplit;
    [ iPureIntro; unfold writeSuccessExactValueWord; reflexivity | ]).
  all: try (repeat iSplit; try iPureIntro; try assumption;
    try bv_solve; try lia; try iFrame).
  all: try (iApply instr_pre_to_body; iNext; liARun).
  Unshelve. all: try prepare_sidecond; try assumption;
    try (rewrite length_take; lia); try bv_solve; try lia; try iFrame.
  Unshelve.
  all: lazymatch goal with |- ?G => fail "exact value suffix" G end.
Qed.

Print Assumptions write_success_exact_value_suffix.

Lemma write_success_exact_value_suffix_pre `{!islaG Sigma} `{!threadG}
    (sp : bv 64) (values : list (bv 64)) (payload : list (bv 8))
    (tail : spec) (P : iProp Sigma) :
  instr_lookup_resources IslaTraces.write_success_blocks.Index.lookup -∗
  IslaTraces.write_success_blocks.Index.spec_instr_resources -∗
  □ instr_pre 0x10190 zesuWriteOutputPayloadCallSpec -∗
  □ instr_pre 0x15d10 zesuEncoderIntPayloadCallSpec -∗
  □ instr_pre 0x14ed4
    (writeSuccessExactValueBaseFeeReturnSpec sp values payload tail P).
Proof.
  iStartProof. iIntros "#Hlookup #Hcode #Houtput #Hint". iModIntro.
  iApply instr_pre_to_body. iNext.
  iApply write_success_exact_value_suffix; iAssumption.
Qed.

Print Assumptions write_success_exact_value_suffix_pre.
