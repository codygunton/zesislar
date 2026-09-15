Require Import ZesuSsz.Automation.All.
From Coq Require Import Lists.List ZArith.ZArith.
Require Import isla.riscv64.riscv64.
From IslaTraces.write_success_blocks Require Import Index HintsValueBlock.
Require Import ZesuSsz.Contracts.IslarisCode.
Require Import ZesuSsz.Contracts.IslarisMachine.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessEncoderIntCall.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessCalls.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessValueSpec.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessValueHandoff.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessOutput.

Local Existing Instance subsume_instr_pre_wand_inst | 1.

#[local] Hint Rewrite Z_to_bv_add Z_to_bv_unsigned :
  lithium_rewrite isla_coq_rewrite.

#[local] Hint Extern 7
  (FindInContext (FindInstrKind ?address ?later) FICSyntactic) =>
  let reduced := eval vm_compute in address in
  first [ constr_eq address reduced; fail 1
        | change (FindInContext (FindInstrKind reduced later) FICSyntactic);
          typeclasses eauto ] : typeclass_instances.

Local Instance : LithiumUnfold (@writeSuccessValuePost) := I.

Lemma write_success_value_suffix `{!islaG Sigma} `{!threadG}
    (sp : bv 64) (values : list (bv 64)) (payload : list (bv 8))
    (tail : spec) (P : iProp Sigma) :
  instr_lookup_resources IslaTraces.write_success_blocks.Index.lookup -∗
  IslaTraces.write_success_blocks.Index.spec_instr_resources -∗
  □ instr_pre 0x10190 zesuWriteOutputCallSpec -∗
  □ instr_pre 0x15d10 zesuEncoderIntCallSpec -∗
  instr_body 0x14ed4
    (writeSuccessValueBaseFeeReturnSpec sp values payload tail P).
Proof.
  move => *. iStartProof.
  iIntros "_ #Hlookup #Hcode #Houtput #Hint".
  iEval (unfold IslaTraces.write_success_blocks.Index.spec_instr_resources)
    in "Hcode".
  liARun.
  Unshelve. all: try prepare_sidecond; try assumption;
    try (rewrite length_take; lia); try bv_solve; try lia; try iFrame.
  Unshelve.
  all: try (iExists (writeOutputEventsAny (sp - 16)%bv (BV 64 8) tail, tt)ₗ;
    repeat iSplit; try iPureIntro; try assumption;
    try bv_solve; try lia; try iFrame).
  Unshelve.
  all: try (iApply instr_pre_to_body; iNext; liARun).
  Unshelve. all: try prepare_sidecond; try assumption;
    try (rewrite length_take; lia); try bv_solve; try lia; try iFrame.
  Unshelve. all: try run_write_success_value_returns.
  all: (iExists tt; iSplit; [|done];
    iIntros "(HreturnedSys & HreturnedX1 & HreturnedX2 & HreturnedX5 &
      HreturnedX10 & HreturnedX11 & HreturnedScratch & HreturnedMmio &
      HreturnedTrace & _)";
    iIntros "HreturnedPC";
    do 224 liAStep; unLET; unfold LET_ID;
    iEval (unfold zesuWriteOutputCallSpec, zesu_c_call); liARun).
  all: try iExists (tail, tt)ₗ.
  all: try (repeat iSplit; try iPureIntro; try assumption;
    try bv_solve; try lia; try iFrame).
  all: try (iApply instr_pre_to_body; iNext; liARun).
  Unshelve. all: try prepare_sidecond; try assumption;
    try (rewrite length_take; lia); try bv_solve; try lia; try iFrame.
  Unshelve.
  all: lazymatch goal with |- ?G => fail "value suffix residual" G end.
Qed.
Print Assumptions write_success_value_suffix.

Lemma write_success_value_suffix_pre `{!islaG Sigma} `{!threadG}
    (sp : bv 64) (values : list (bv 64)) (payload : list (bv 8))
    (tail : spec) (P : iProp Sigma) :
  instr_lookup_resources IslaTraces.write_success_blocks.Index.lookup -∗
  IslaTraces.write_success_blocks.Index.spec_instr_resources -∗
  □ instr_pre 0x10190 zesuWriteOutputCallSpec -∗
  □ instr_pre 0x15d10 zesuEncoderIntCallSpec -∗
  □ instr_pre 0x14ed4
    (writeSuccessValueBaseFeeReturnSpec sp values payload tail P).
Proof.
  iStartProof. iIntros "#Hlookup #Hcode #Houtput #Hint". iModIntro.
  iApply instr_pre_to_body. iNext.
  iApply write_success_value_suffix; iAssumption.
Qed.
Print Assumptions write_success_value_suffix_pre.
