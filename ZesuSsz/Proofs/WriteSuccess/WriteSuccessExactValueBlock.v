Require Import ZesuSsz.Automation.AllLegacy.
From Coq Require Import Lists.List ZArith.ZArith.
Require Import isla.riscv64.riscv64.
From IslaTraces.write_success_blocks Require Import Index HintsValueBlock.
Require Import ZesuSsz.Contracts.IslarisCode.
Require Import ZesuSsz.Contracts.IslarisMachine.
Require Import ZesuSsz.Contracts.IslarisMemory.
Require Import ZesuSsz.Export.Snapshots.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccess.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessCallAbi.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessExactEncoderBytes.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessExactEncoderIntCall.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessExactValueSpec.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessExactValueSuffix.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessObservation.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessOutputSemantic.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessLoopMemory.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessPayloadCall.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessValueBlock.

Import ListNotations.

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

Ltac run_write_success_exact_values :=
  lazymatch goal with
  | |- instr_body 0x14f04 _ => idtac
  | _ =>
      first
        [ progress unLET
        | progress iEval (unfold zesuWriteOutputPayloadCallSpec, zesu_c_call)
        | progress iEval (unfold zesuEncoderIntPayloadCallSpec)
        | progress iEval (unfold encoderBytesExactCallSpec, zesu_c_call)
        | liAStep
        | progress prepare_sidecond
        | reflexivity
        | vm_compute
        | bv_solve
        | lia ];
      run_write_success_exact_values
  end.

Ltac run_write_success_exact_value_returns :=
  lazymatch goal with
  | |- environments.envs_entails _ ((_ -∗ _) ∗ True) =>
      iSplit; [|done]; liARun; run_write_success_exact_value_returns
  | |- environments.envs_entails _
      (subsume (instr ?address
        (IslaTraces.write_success_blocks.Index.lookup ?address)) _ _) =>
      iEval (vm_compute [IslaTraces.write_success_blocks.Index.lookup]);
      iApply subsume_instr_some_pre;
      run_write_success_exact_value_returns
  | _ => idtac
  end.

Lemma write_success_exact_value_block `{!islaG Sigma} `{!threadG}
    (P : iProp Sigma) :
  instr_lookup_resources IslaTraces.write_success_blocks.Index.lookup -∗
  IslaTraces.write_success_blocks.Index.spec_instr_resources -∗
  □ instr_pre 0x10190 zesuWriteOutputPayloadCallSpec -∗
  □ instr_pre 0x15d10 zesuEncoderIntPayloadCallSpec -∗
  □ instr_pre 0x15c6c encoderBytesExactCallSpec -∗
  instr_body 0x14e88 (writeSuccessExactValueSpec P).
Proof.
  move => *. iStartProof. iIntros "_ #Hlookup #Hcode #Houtput #Hint #Hbytes". iEval (unfold IslaTraces.write_success_blocks.Index.spec_instr_resources) in "Hcode". liARun.
  Unshelve. all: try prepare_sidecond; try assumption; try (cbn; rewrite ?length_take ?length_drop; lia); try bv_solve; try lia; try iFrame.
  Unshelve. all: try iFrame; try prepare_sidecond; try assumption; try bv_solve; try lia. all: lazymatch goal with |- ?G => fail "exact value prefix" G end.
  Unshelve. all: try run_write_success_exact_values. Unshelve. all: try prepare_sidecond; try assumption; try bv_solve; try lia; try iFrame.
  Unshelve. all: try iEval (unfold LET_ID). all: try run_write_success_exact_value_returns. Unshelve. all: try prepare_sidecond; try assumption;
  try (cbn; rewrite ?length_take ?length_drop; lia); try bv_solve; try lia; try iFrame. Unshelve. all: try prepare_sidecond; try assumption;
  try (cbn; rewrite ?length_take ?length_drop; lia); try bv_solve; try lia; try iFrame. all: lazymatch goal with |- ?G => fail "exact value middle" G end.
  Unshelve. iExists (writeSuccessExactValueEventsAfter0 sp values payload tail, tt)ₗ. liARun. Unshelve. all: try prepare_sidecond; try assumption; try (cbn [writeSuccessValueWord]; lia); try bv_solve; try lia; try iFrame.
  Unshelve. all: try iEval (unfold LET_ID). all: try run_write_success_exact_value_returns. Unshelve. all: try prepare_sidecond; try assumption;
  try (cbn [writeSuccessValueWord]; lia); try bv_solve; try lia; try iFrame. Unshelve. all: try run_write_success_exact_value_returns. all: try (rewrite length_take; lia). all: try (iExists (writeSuccessExactValueEventsAfter1 sp values payload tail, tt)ₗ; liARun).
  Unshelve. all: try prepare_sidecond; try assumption; try (rewrite length_take; lia); try bv_solve; try lia; try iFrame. Unshelve. all: try run_write_success_exact_value_returns.
  Unshelve. all: try prepare_sidecond; try assumption; try (rewrite length_take; lia); try bv_solve; try lia; try iFrame. all: try (iExists (writeSuccessExactValueEventsAfter2 sp values payload tail, tt)ₗ; liARun).
  Unshelve. all: try prepare_sidecond; try assumption; try (rewrite length_take; lia); try bv_solve; try lia; try iFrame. Unshelve. all: try run_write_success_exact_value_returns. Unshelve.
  all: try (iExists (writeSuccessExactValueEventsAfter2 sp values payload tail, tt)ₗ; liARun). Unshelve. all: try prepare_sidecond; try assumption; try (rewrite length_take; lia); try bv_solve; try lia; try iFrame.
  Unshelve. all: try run_write_success_exact_value_returns. Unshelve. all: try (iExists (writeSuccessExactValueEventsAfterInts sp values payload tail, tt)ₗ; liARun). Unshelve. all: try prepare_sidecond; try assumption;
  try (rewrite length_take; lia); try bv_solve; try lia; try iFrame. Unshelve. all: try run_write_success_exact_value_returns. Unshelve. all: try (iExists (_, writeSuccessExactValueEventsAfterExtra sp values tail, payload,
  Z_to_bv 64 (85700 + 4), sp, writeSuccessExactValueWord values 5, writeSuccessExactValueWord values 4, tt)ₗ; liARun). Unshelve. all: try prepare_sidecond; try assumption;
  try (rewrite length_take; lia); try bv_solve; try lia; try iFrame. Unshelve. all: try run_write_success_exact_value_returns. Unshelve. all: try prepare_sidecond; try assumption;
  try (rewrite length_take; lia); try bv_solve; try lia; try iFrame. Unshelve. all: lazymatch goal with | |- environments.envs_entails _ (subsume _ _ _) =>
  iRename select ((bv_unsigned sp - 16) ↦ₘ? 16)%I into "HstackHigh"; rewrite /subsume; iIntros "HstackLow"; iAssert ((bv_unsigned sp - 48) ↦ₘ? 48)%I with "[HstackLow HstackHigh]" as "Hstack"; [ iApply (mem_mapsto_uninit_combine 32 with "HstackLow [HstackHigh]"); [lia|];
  replace (bv_unsigned sp - 48 + 32) with (bv_unsigned sp - 16) by lia; iExact "HstackHigh" | iDestruct (encoder_bytes_uninit_48_to_words sp with "Hstack") as (w0 w1 w2 w3 w4 w5) "(H0 & H1 & H2 & H3 & H4 & H5)"; iExists (w5, w4, w3, w2, w1, w0, tt)ₗ; liARun ]
  | _ => idtac end. all: try prepare_sidecond; try assumption; try bv_solve; try lia; try iFrame. all: try run_write_success_exact_value_returns.
  Unshelve. all: try prepare_sidecond; try assumption; try (bv_simplify_arith select (bv_unsigned sp `mod` 16 = 0)); try bv_solve; try lia; try iFrame. Unshelve. all: try run_write_success_exact_value_returns.
  Unshelve. all: try (iExists (take 69 values, sp, tt)ₗ; liARun). Unshelve. all: try prepare_sidecond; try assumption; try (rewrite length_take; lia); try bv_solve; try lia; try iFrame. Unshelve. all: try (iRename select (encoderBytesExactOutputResources _ _ _ _ _ _ _)%I into "HbytesFrame";
  iEval (unfold encoderBytesExactOutputResources) in "HbytesFrame"; iDestruct "HbytesFrame" as "(Hframe6 & Hframe2 & Hframe8 & Hframe9 & Hframe0 & Hframe1 & Hframe2mem & Hframe3 & Hframe4 & Hframe5 & HframeRegs)"). all: try iEval (unfold encoderBytesExactOutputResources) in "*". all: try iFrame.
  all: try (repeat iSplit; try iPureIntro; try assumption; try (rewrite length_take; lia); try bv_solve; try lia). all: try run_write_success_exact_value_returns. Unshelve. all: try prepare_sidecond; try assumption; try (rewrite length_take; lia); try bv_solve; try lia; try iFrame.
  Unshelve. all: try (iApply instr_pre_to_body; iNext; liARun). Unshelve. all: try prepare_sidecond; try assumption; try (rewrite length_take; lia); try bv_solve; try lia; try iFrame. Unshelve. all: try iExists (writeOutputEvents (sp + 1588)%bv (BV 64 32) (writeSuccessValueBlockHash values) (writeSuccessExactValueIntEvent sp values 8 tail), tt)ₗ.
  all: try (iSplit; [iPureIntro; unfold writeSuccessExactValueWord; reflexivity |]). all: try (repeat iSplit; try iPureIntro; try assumption; try bv_solve; try lia; try iFrame). iPoseProof (write_success_exact_value_suffix_pre sp values payload tail P with
  "Hlookup Hcode Houtput Hint") as "#HvalueSuffix". iApply (instr_pre_wand 0x14ed4 0x14ed4 true true with "HvalueSuffix"); [done | reflexivity |]. iIntros "Hreturn". iEval (unfold writeSuccessExactValueBaseFeeReturnSpec).
  iExists b8, b9, w2. iFrame. iDestruct "Hreturn" as "(HretSys & Hret1 & Hret2 & Hret5 & Hret10 & Hret11 & HretStack & HretMmio & HretTrace & _)". have Hret : Z_to_bv 64 (85712 + 4) = BV 64 0x14ed4 by (apply bv_eq; vm_compute).
  iEval (rewrite Hret) in "Hret1". iFrame "Hret1".
  zesu_run. Unshelve. all: zesu_finish.
Qed.

Print Assumptions write_success_exact_value_block.
