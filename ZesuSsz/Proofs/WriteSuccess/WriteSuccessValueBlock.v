Require Import ZesuSsz.Automation.All.
Require Import ZesuSsz.Automation.InstrPre.
Local Remove Hints subsume_instr_pre_zesu_inst : typeclass_instances.
Require Import ZesuMachineMap.Machine.
From Coq Require Import Lists.List ZArith.ZArith.
Require Import isla.riscv64.riscv64.
From IslaTraces.write_success_blocks Require Import Index HintsValueBlock.
Require Import ZesuSsz.Contracts.IslarisMachine.
Require Import ZesuSsz.Contracts.IslarisCode.
Local Remove Hints subsume_instr_some_pre_inst : typeclass_instances.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccess.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessCallAbi.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessCalls.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessEncoderCalls.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessHeaderBlock.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessHeaderSpec.
Require Export ZesuSsz.Proofs.WriteSuccess.WriteSuccessValueSpec.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessValueHandoff.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessValueSuffix.

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

Ltac run_write_success_values :=
  lazymatch goal with
  | |- instr_body 0x14f04 _ => idtac
  | _ =>
      first
        [ progress unLET
        | progress iEval (unfold zesuWriteOutputCallSpec, zesu_c_call)
        | progress iEval (unfold zesuEncoderIntCallSpec)
        | progress iEval (unfold zesuEncoderBytesCallSpec, zesu_c_call)
        | liAStep
        | progress prepare_sidecond
        | reflexivity
        | vm_compute
        | bv_solve
        | lia ];
      run_write_success_values
  end.


Local Instance : LithiumUnfold (@writeSuccessValueSpec) := I.
Local Instance : LithiumUnfold (@writeSuccessValuePost) := I.

Lemma write_success_value_block `{!islaG Sigma} `{!threadG}
    (P : iProp Sigma) :
  instr_lookup_resources IslaTraces.write_success_blocks.Index.lookup -∗
  IslaTraces.write_success_blocks.Index.spec_instr_resources -∗
  □ instr_pre 0x10190 zesuWriteOutputCallSpec -∗
  □ instr_pre 0x15d10 zesuEncoderIntCallSpec -∗
  □ instr_pre 0x15c6c zesuEncoderBytesCallSpec -∗
  instr_body 0x14e88 (writeSuccessValueSpec P).
Proof.
  move => *.
  iStartProof.
  iIntros "#Hlookup #Hcode #Houtput #Hint #Hbytes".
  iEval (unfold IslaTraces.write_success_blocks.Index.spec_instr_resources)
    in "Hcode".
  liARun.
  Unshelve.
  all: try prepare_sidecond. all: try assumption.
  all: try (cbn; rewrite ?length_take ?length_drop; lia).
  all: try bv_solve. all: try lia. all: try iFrame.
  Unshelve.
  all: try iFrame.
  all: try prepare_sidecond. all: try assumption.
  all: try bv_solve. all: try lia.
  all: lazymatch goal with |- ?G => fail "side condition" G end.
  Unshelve.
  all: try run_write_success_values.
  Unshelve.
  all: try prepare_sidecond. all: try assumption.
  all: try bv_solve. all: try lia. all: try iFrame.
  Unshelve.
  all: try iEval (unfold LET_ID).
  run_write_success_value_returns.
  Unshelve.
  all: try prepare_sidecond. all: try assumption.
  all: try (cbn; rewrite ?length_take ?length_drop; lia).
  all: try bv_solve. all: try lia. all: try iFrame.
  Unshelve.
  all: try prepare_sidecond. all: try assumption.
  all: try (cbn; rewrite ?length_take ?length_drop; lia).
  all: try bv_solve. all: try lia. all: try iFrame.
  all: lazymatch goal with |- ?G => fail "side condition" G end.
  Unshelve.
  iExists
    (writeOutputEventsAny (sp - 16)%bv (BV 64 8)
       (writeOutputEventsAny (sp + 1588)%bv (BV 64 32)
          (writeOutputEventsAny (sp - 16)%bv (BV 64 8) tail)),
     payload, tt)ₗ.
  liARun.
  Unshelve.
  all: try prepare_sidecond. all: try assumption.
  all: try (cbn [writeSuccessValueWord]; lia).
  all: try bv_solve. all: try lia. all: try iFrame.
  Unshelve.
  all: try iEval (unfold LET_ID).
  run_write_success_value_returns.
  Unshelve.
  all: try prepare_sidecond. all: try assumption.
  all: try (cbn [writeSuccessValueWord]; lia).
  all: try bv_solve. all: try lia. all: try iFrame.
  Unshelve.
  run_write_success_value_returns.
  iPoseProof (write_success_value_suffix sp values payload tail P with
    "Hcode Houtput Hint Hbytes") as "#HvalueSuffixBody".
  iExists tt. iSplit; [|done].
  iIntros "(HreturnedSys & HreturnedX1 & HreturnedX2 & HreturnedX5 &
    HreturnedX10 & HreturnedX11 & HreturnedScratch & HreturnedMmio &
    HreturnedTrace & _)".
  iIntros "HreturnedPC".
  have Hret : Z_to_bv 64 (85712 + 4) = BV 64 0x14ed4 by bv_solve.
  iEval (rewrite Hret) in "HreturnedX1 HreturnedPC".
  iAssert (writeSuccessValueBaseFeeReturnSpec sp values payload tail P)%I
    with "[-HreturnedPC]"
    as "HsuffixEntry".
  { rewrite /writeSuccessValueBaseFeeReturnSpec. iExists b8, b9.
    iFrame "∗".
    iRename select ("x6" ↦ᵣ RVal_Bits b10)%I into "Hx6".
    iAssert (("x6" ↦ᵣ: fun r6 => ⌜valu_has_shape r6 (BitsShape 64)⌝))%I
      with "[Hx6]" as "Hx6shape".
    { rewrite reg_mapsto_pred_eq /reg_mapsto_pred_def.
      iExists (RVal_Bits b10). iSplit; first iExact "Hx6".
      iPureIntro. cbn. reflexivity. }
    iFrame "Hx6shape".
    Unshelve. all: try zesu_finish.
    all: repeat iSplit; try iPureIntro; try assumption; try zesu_finish.
 }
  iEval (rewrite instr_pre'_eq) in "HvalueSuffixBody".
  iDestruct ("HvalueSuffixBody" with "HsuffixEntry") as (ins)
    "[HsuffixInstr HsuffixBody]".
  iEval (rewrite /instr_lookup_resources) in "Hcode".
  iPoseProof ("Hcode" $! 85716 with "[]") as "#Hactual".
  { iPureIntro. vm_compute. eexists. reflexivity. }
  rewrite instr_eq /instr_def.
  iDestruct "Hactual" as (tblActual instrBV1 Hb1 Hval1) "#HtblActual".
  iDestruct "HsuffixInstr" as (tblSuffix instrBV2 Hb2 Hval2) "#HtblSuffix".
  iDestruct (instr_table_agree with "HtblActual HtblSuffix") as %Hsame.
  subst tblSuffix.
  have Hb : instrBV1 = instrBV2 by (rewrite Hb1 in Hb2; simplify_eq).
  subst instrBV2.
  have Hins : ins = IslaTraces.write_success_blocks.Index.lookup 85716 by congruence.
  iEval (rewrite Hins /=) in "HsuffixBody".
  have Hpc : Z_to_bv 64 85716 = (85716%bv) by bv_solve.
  iEval (rewrite Hpc) in "HsuffixBody".
  iApply ("HsuffixBody" with "HreturnedPC").
Qed.

Print Assumptions write_success_value_block.
