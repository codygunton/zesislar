Require Import ZesuSsz.Automation.AllLegacy.
Require Import isla.riscv64.riscv64.
From IslaTraces.write_success_blocks Require Import Index HintsAuthorizationsLoop.
Require Import ZesuSsz.Contracts.IslarisMachine.
Require Import ZesuSsz.Contracts.IslarisCode.
Require Import ZesuSsz.Contracts.IslarisMemory.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessEncoderCalls.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessAuthorizationsSpec.

Local Remove Hints subsume_instr_pre'_inst : typeclass_instances.
Local Existing Instance subsume_instr_pre_wand_inst | 1.

Lemma write_success_authorizations_first_u256 `{!islaG Sigma} `{!threadG}
    (P : iProp Sigma) :
  instr_lookup_resources IslaTraces.write_success_blocks.Index.lookup -∗
  IslaTraces.write_success_blocks.Index.spec_instr_resources -∗
  □ instr_pre 0x15cb0 zesuEncoderU256CallSpec -∗
  instr_body 0x155bc
    (writeSuccessAuthorizationsCopiedSpec AuthorizationsOutput P) -∗
  instr_body 0x155a4
    (writeSuccessAuthorizationsCopiedSpec AuthorizationsFirstU256 P).
Proof.
  move => *.
  iStartProof.
  iIntros "_ #Hlookup #Hcode #Hu256 Hnext".
  iEval (unfold IslaTraces.write_success_blocks.Index.spec_instr_resources)
    in "Hcode".
  run_write_success_authorizations_chunk 0x155bc.
  Unshelve. all: try run_write_success_authorizations_return 0x155bc.
  all: try prepare_sidecond.
  all: try assumption.
  all: try (cbn; rewrite ?length_take ?length_drop; lia).
  all: try iFrame.
  all: try bv_solve.
  all: try lia.
  Unshelve.
  iExists
    (tail, suffix, prefix, prefix ++ suffix, processed,
     (processed + S remaining)%nat, base, tt)ₗ.
  liARun.
  Unshelve.
  all: try prepare_sidecond.
  all: try (cbn; rewrite ?length_take ?length_drop; lia).
  all: try bv_solve.
  all: try lia.
  all: try iFrame.
  Unshelve. all: try liAStep.
  Unshelve.
  all: try prepare_sidecond.
  all: try (cbn; rewrite ?length_take ?length_drop; lia).
  all: try bv_solve.
  all: try lia.
  Unshelve. all: try liARun.
  Unshelve.
  all: try prepare_sidecond.
  all: try (cbn; rewrite ?length_take ?length_drop; lia).
  all: try bv_solve.
  all: try lia.
  Unshelve.
  have HscratchStart0 :
      Z.to_nat (bv_unsigned sp + 1744 - (bv_unsigned sp + 1744)) = 0%nat.
  {
    replace (bv_unsigned sp + 1744 - (bv_unsigned sp + 1744))%Z with 0%Z
      by lia. reflexivity. }
  have HscratchStart1 :
      Z.to_nat
      (bv_unsigned sp + 1752 -
       (bv_unsigned sp + 1744 + (0 + 8)%nat)) = 0%nat.
  {
    replace
      (bv_unsigned sp + 1752 -
       (bv_unsigned sp + 1744 + (0 + 8)%nat))%Z with 0%Z by lia.
    reflexivity. }
  have HscratchStart2 :
      Z.to_nat
      (bv_unsigned sp + 1760 -
       (bv_unsigned sp + 1744 + (0 + 8)%nat + (0 + 8)%nat)) = 0%nat.
  {
    replace
      (bv_unsigned sp + 1760 -
       (bv_unsigned sp + 1744 + (0 + 8)%nat + (0 + 8)%nat))%Z with 0%Z
      by lia. reflexivity. }
  have HscratchStart3 :
      Z.to_nat
      (bv_unsigned sp + 1768 -
       (bv_unsigned sp + 1744 + (0 + 8)%nat + (0 + 8)%nat +
        (0 + 8)%nat)) = 0%nat.
  {
    replace
      (bv_unsigned sp + 1768 -
       (bv_unsigned sp + 1744 + (0 + 8)%nat + (0 + 8)%nat +
        (0 + 8)%nat))%Z with 0%Z by lia.
    reflexivity. }
  iRename select
    (_ ↦ₘ∗ take _ (drop _ (drop _ (drop _ current))))%I
    into "HscratchPrefix3".
  iRename select
    (_ ↦ₘ∗ drop _ (drop _ (drop _ (drop _ current))))%I
    into "HscratchSuffix4".
  iRename select ((bv_unsigned sp + 1768) ↦ₘ _)%I
    into "HscratchWord3".
  iEval (rewrite HscratchStart0 HscratchStart1 HscratchStart2
    HscratchStart3) in "HscratchPrefix3".
  iEval (rewrite HscratchStart0 HscratchStart1 HscratchStart2
    HscratchStart3) in "HscratchSuffix4".
  iEval (rewrite HscratchStart0 HscratchStart1 HscratchStart2
    HscratchStart3) in "HscratchWord3".
  iPoseProof (mem_mapsto_array_recombine_u64_read _ _ _ _ _
    with "HscratchPrefix3 HscratchSuffix4 HscratchWord3 [] [] []")
    as "HscratchRest3".
  { iPureIntro. cbn. lia. }
  { iPureIntro. cbn. lia. }
  { iPureIntro. cbn. rewrite ?length_take ?length_drop. lia. }
  iRename select
    (_ ↦ₘ∗ take _ (drop _ (drop _ current)))%I
    into "HscratchPrefix2".
  iRename select ((bv_unsigned sp + 1760) ↦ₘ _)%I
    into "HscratchWord2".
  iEval (rewrite HscratchStart0 HscratchStart1 HscratchStart2)
    in "HscratchPrefix2".
  iEval (rewrite HscratchStart0 HscratchStart1 HscratchStart2)
    in "HscratchWord2".
  iPoseProof (mem_mapsto_array_recombine_u64_read _ _ _ _ _
    with "HscratchPrefix2 HscratchRest3 HscratchWord2 [] [] []")
    as "HscratchRest2".
  { iPureIntro. cbn. lia. }
  { iPureIntro. cbn. lia. }
  { iPureIntro. cbn. rewrite ?length_take ?length_drop. lia. }
  iRename select
    (_ ↦ₘ∗ take _ (drop _ current))%I into "HscratchPrefix1".
  iRename select ((bv_unsigned sp + 1752) ↦ₘ _)%I
    into "HscratchWord1".
  iEval (rewrite HscratchStart0 HscratchStart1) in "HscratchPrefix1".
  iEval (rewrite HscratchStart0 HscratchStart1) in "HscratchWord1".
  iPoseProof (mem_mapsto_array_recombine_u64_read _ _ _ _ _
    with "HscratchPrefix1 HscratchRest2 HscratchWord1 [] [] []")
    as "HscratchRest1".
  { iPureIntro. cbn. lia. }
  { iPureIntro. cbn. lia. }
  { iPureIntro. cbn. rewrite ?length_take ?length_drop. lia. }
  iRename select (_ ↦ₘ∗ take _ current)%I into "HscratchPrefix0".
  rewrite /subsume. iIntros "HscratchWord0".
  iEval (rewrite HscratchStart0) in "HscratchPrefix0".
  iEval (rewrite HscratchStart0) in "HscratchWord0".
  iPoseProof (mem_mapsto_array_recombine_u64_read _ _ _ _ _
    with "HscratchPrefix0 HscratchRest1 HscratchWord0 [] [] []")
    as "Hcurrent".
  { iPureIntro. cbn. lia. }
  { iPureIntro. cbn. lia. }
  { iPureIntro. cbn. rewrite ?length_take ?length_drop. lia. }
  liARun.
  Unshelve.
  all: try prepare_sidecond.
  all: try (cbn; rewrite ?length_take ?length_drop; lia).
  all: try bv_solve.
  all: try lia.
  all: try iFrame.
Qed.
