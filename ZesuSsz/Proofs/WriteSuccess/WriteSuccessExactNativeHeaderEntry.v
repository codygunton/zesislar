Require Import ZesuSsz.Automation.All.
Require Import ZesuSsz.Automation.RegPacking.
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessExactNativeLoadSpec.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessExactHeaderValue.
From ZesuSsz.Proofs.WriteSuccess Require Import
  WriteSuccessHeaderSpec WriteSuccessExactHeaderSpec WriteSuccessExactValueSpec
  WriteSuccessNativeContract.
Lemma native_load_header_entry `{!islaG Sigma} `{!threadG}
    sp decoded object bytes values payload tail (P : iProp Sigma)
    (Hbytes : length bytes = 720%nat)
    (Halign16 : bv_unsigned sp `mod` 16 = 0)
    (Hupper : bv_unsigned sp + 1896 < machineRamEnd defaultMap) :
  exactNativeLoadState sp decoded object
    ((bv_unsigned sp + 312) ↦ₘ∗ bytes ∗
     (bv_unsigned sp + 1032) ↦ₘ? 864 ∗
     mmio_range (machineOutputAddress defaultMap) 16 ∗
     spec_trace (writeSuccessExactHeaderEvents sp bytes
       (writeSuccessExactValueEvents sp values payload tail)) ∗
     writeSuccessNativeStaticResources ∗
     ((bv_unsigned sp ↦ₘ? 104 ∗ (bv_unsigned sp + 120) ↦ₘ? 192 ∗
       bv_unsigned decoded ↦ₘ∗ object) -∗
       writeSuccessExactHeaderValueTransition P sp bytes values payload tail))%I -∗
  writeSuccessExactHeaderValueSpec P sp bytes values payload tail.
Proof.
  rewrite /exactNativeLoadState.
  iIntros "(Hsys & Hregs & H2 & H8 & Hobject & Hstack & %Hlength & %HdecodedAlign & %HdecodedLower & %HdecodedUpper & %Halign8 & %Hlower & %HloadUpper & Hframe & _)".
  iDestruct "Hframe" as "(Hsource & Hhigh & Hmmio & Htrace & Hstatic & Htransition)".
  iAssert (reg_col writeSuccessHeaderRegShapes) with "[H8 Hregs]" as "Hheader".
  { iApply (reg_col_mixed_collect [("x8", decoded)] [] exactNativeLoadOtherShapes).
    - rewrite /writeSuccessHeaderRegShapes /writeSuccessHeaderRegisters
        /exactNativeLoadOtherShapes /exactNativeLoadOtherRegisters /=. solve_Permutation.
    - cbn. iFrame. }
  rewrite /writeSuccessExactHeaderValueSpec.
  iFrame "Hsys Hheader H2 Hsource Hhigh Hmmio Htrace Hstatic".
  zesu_run.
  iRename select (bv_unsigned sp ↦ₘ? 104)%I into "Hprefix".
  iRename select ((_ ↦ₘ? 192))%I into "Hsuffix".
  iAssert (writeSuccessExactHeaderValueTransition P sp bytes values payload tail)%I
    with "[Hobject Htransition Hprefix Hsuffix]" as "Hbuilt".
  { iApply "Htransition".
    replace (bv_unsigned sp + 120)%Z with (bv_unsigned sp + 104 + 16)%Z by lia.
    iFrame. }
  iEval (unfold writeSuccessExactHeaderValueTransition) in "Hbuilt".
  repeat iDestruct "Hbuilt" as "[? Hbuilt]".
  iFrame.
  Unshelve. all: zesu_finish.
Qed.
Print Assumptions native_load_header_entry.
