Require Import ZesuSsz.Automation.AllLegacy.
Require Import ZesuMachineMap.Machine.
From Coq Require Import Lists.List ZArith.ZArith.
Require Import isla.riscv64.riscv64.
Require Import InstrSpecs.Specs.
From IslaTraces.write_success_blocks Require Import
  Index HintsHashesLoop HintsBlobHashesLoop HintsStorageKeysLoop.
Require Import IslaTraces.write_success_66.a153dc_spec.
Require Import ZesuSsz.Contracts.IslarisMachine.
Require Import ZesuSsz.Contracts.IslarisCode.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessBlobHashesSpec.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessLoopCommon.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessBlobHashesSegment02State.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessBlobHashesSegment02ARawFrame.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessBlobHashesSegment02ARawRegisters.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessBlobHashesSegment02ARecombine.

Local Remove Hints a153dc_spec_inst : typeclass_instances.

Import ListNotations.
Local Remove Hints subsume_instr_pre'_inst : typeclass_instances.
Local Existing Instance subsume_instr_pre_wand_inst | 1.
#[local] Hint Extern 7
  (FindInContext (FindInstrKind ?address ?later) FICSyntactic) =>
  let reduced := eval vm_compute in address in
  first [ constr_eq address reduced; fail 1
        | change (FindInContext (FindInstrKind reduced later) FICSyntactic);
          typeclasses eauto ] : typeclass_instances.

Lemma write_success_blob_hashes_chunk0b_153dc_core
    `{!islaG Sigma} `{!threadG} (P : iProp Sigma)
    (sp pointer : bv 64) (base : Z) (total processed remaining : nat)
    (bytes : list (bv 8)) (tail : spec) :
  instr_lookup_resources IslaTraces.write_success_blocks.Index.lookup -∗
  IslaTraces.write_success_blocks.Index.spec_instr_resources -∗
  instr_body 0x153e0 (writeSuccessBlobHashesLoopSpec P) -∗
  instr_body 0x153dc (writeSuccessBlobHashesSegment02State P sp pointer base
    total processed remaining bytes tail).
Proof.
  move => *.
  iStartProof.
  iIntros "_ #Hlookup #Hcode Hnext".
  iEval (unfold IslaTraces.write_success_blocks.Index.spec_instr_resources)
    in "Hcode".
  liARun.
  iExists
    (drop (32 * processed) bytes,
      default (BV 8 0) (bytes !! (32 * processed + 18)%nat), tt)ₗ.
  liARun.
  Unshelve.
  all: try rewrite (write_success_blob_hashes_region_start_18
    pointer base processed H1).
  all: try exact
    (write_success_blob_hashes_take_18 bytes processed remaining H0).
  all: prepare_sidecond.
  all: try solve_zesu_ld_array_at.
  all: try (apply bv_eq; rewrite bv_and_unsigned; assumption).
  all: try (bv_simplify_arith H1; bv_solve).
  Unshelve. all: try liARun.
  iRename select (base ↦ₘ∗ take (32 * processed + 18) bytes)%I into "Hleft".
  iRename select
    ((base + 1 * (32 * processed + 18 + 1)%nat) ↦ₘ∗
      drop (32 * processed + 18 + 1) bytes)%I into "Hright".
  have HrightAddress :
      (base + 1 * (32 * processed + 18 + 1)%nat)%Z =
        (base + Z.of_nat (32 * processed + 19))%Z.
  { f_equal. lia. }
  have HrightDrop :
      drop (32 * processed + 18 + 1) bytes =
        drop (32 * processed + 19) bytes.
  { f_equal. lia. }
  iEval (rewrite HrightAddress HrightDrop) in "Hright".
  iPoseProof (write_success_blob_hashes_segment02_raw_frame pointer base
    processed remaining bytes with "Hleft Hright [] []") as
    "(Hdone & Hprefix & Hsuffix)".
  { iPureIntro. exact H0. }
  { iPureIntro. exact H1. }
  have HbyteLookup :
      drop (32 * processed) bytes !! 18%nat =
        Some (default (BV 8 0)
          (bytes !! (32 * processed + 18)%nat)).
  { rewrite lookup_drop.
    replace (32 * processed + 18)%nat with
      (18 + 32 * processed)%nat by lia.
    destruct (bytes !! (18 + 32 * processed)%nat) eqn:Hlookup; first done.
    apply lookup_ge_None in Hlookup. lia. }
  rewrite !Z.add_0_r.
  iFrame "Hprefix Hsuffix".
  repeat iSplit; try iPureIntro; try exact HbyteLookup; try lia.
  - rewrite length_drop H0. lia.
  - rewrite instr_pre'_eq. iNext. iIntros "Hpost".
    iRename select (reg_col _) into "HotherPost".
    iDestruct "Hpost" as
      "(HsysPost & Hx28Post & Hx19Post & HbytePost & HprefixPost &
        HsuffixPost & _)".
    iPoseProof (write_success_blob_hashes_segment02a_recombine_lbu pointer base
      processed bytes
      (default (BV 8 0) (bytes !! (32 * processed + 18)%nat)) with
      "[] [] Hdone HbytePost HprefixPost HsuffixPost") as "HarrayPost".
    { iPureIntro. exact H1. }
    { iPureIntro. exact HbyteLookup. }
    iPoseProof (write_success_blob_hashes_segment02_raw_registers
      (default (BV 8 0) (bytes !! (32 * processed + 18)%nat)) with
      "HotherPost Hx28Post") as "Hother".
    iApply "Hnext".
    rewrite /writeSuccessBlobHashesLoopSpec.
    iExists sp, pointer, base, (processed + S remaining)%nat, processed,
      remaining, bytes, tail.
    iFrame.
    iSplit.
    + iRename select (mmio_range _ 16) into "HmmioPost".
      iExact "HmmioPost".
    + iSplit.
      * rewrite /writeSuccessFixedWidthArrayInvariant.
      repeat iSplit; try iPureIntro; try assumption; try lia.
      * iSplit; last done.
        rewrite instr_pre'_eq. iNext. iIntros "HexitState".
        iRename select
          (_ -∗ ∃ ins : option isla_trace, instr _ ins ∗ _)%I into "Hexit".
        iApply ("Hexit" with "HexitState").
Qed.

Print Assumptions write_success_blob_hashes_chunk0b_153dc_core.
