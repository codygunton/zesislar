From Coq Require Import Lists.List ZArith.ZArith.
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Experiments.WriteSuccessHashesLoop.
Require Import ZesuSsz.Experiments.WriteSuccessLoopCommon.
Require Import ZesuSsz.Contracts.IslarisMachine.

Definition writeSuccessSuffixHashesLoopResources
    `{!islaG Sigma} `{!threadG}
    (sp pointer : bv 64) (base : Z)
    (total processed remaining : nat) (bytes : list (bv 8))
    (tail : spec) (P : iProp Sigma) : iProp Sigma :=
  (reg_col writeSuccessHashesOtherRegShapes ∗
   "x2" ↦ᵣ RVal_Bits sp ∗
   "x9" ↦ᵣ RVal_Bits pointer ∗
   base ↦ₘ∗ bytes ∗ writeSuccessHashesScratch sp ∗
   mmio_range 0x2401a0c0 16 ∗
   spec_trace (writeSuccessHashesEvents sp (S remaining) tail) ∗ P ∗
   writeSuccessFixedWidthArrayInvariant
     sp pointer base total processed remaining bytes ∗
   instr_pre 0x158e0
     (writeSuccessHashesLoopExit sp base total bytes tail P) ∗ True)%I.

Global Instance : LithiumUnfold (@writeSuccessSuffixHashesLoopResources) := I.

Lemma write_success_suffix_hashes_nonzero_loop_wand
    `{!islaG Sigma} `{!threadG}
    (value sp pointer : bv 64) (base : Z)
    (total processed remaining : nat) (bytes : list (bv 8))
    (tail : spec) (P : iProp Sigma)
    (Hvalue : value = Z_to_bv 64 (Z.of_nat (S remaining))) :
  (reg_col zesu_ram_sys_regs ∗
   "x8" ↦ᵣ RVal_Bits value ∗
   writeSuccessSuffixHashesLoopResources
     sp pointer base total processed remaining bytes tail P) -∗
  writeSuccessHashesLoopSpec P.
Proof.
  iIntros "(Hsys & H8 & Hrest)".
  subst value.
  iEval (unfold writeSuccessSuffixHashesLoopResources) in "Hrest".
  iDestruct "Hrest" as
    "(Hother & H2 & H9 & Hbytes & Hscratch & Hmmio & Htrace & HP &
      Hinvariant & Hnext & _)".
  rewrite /writeSuccessHashesLoopSpec.
  iExists sp, pointer, base, total, processed, remaining, bytes, tail.
  iFrame "Hsys Hother H2 H8 H9 Hbytes Hscratch Hmmio Htrace HP
    Hinvariant Hnext".
Qed.

Definition writeSuccessSuffixHashesZeroResources
    `{!islaG Sigma} `{!threadG}
    (sp pointer : bv 64) (base : Z)
    (total : nat) (bytes : list (bv 8))
    (tail : spec) (P : iProp Sigma) : iProp Sigma :=
  (reg_col writeSuccessHashesOtherRegShapes ∗
   "x2" ↦ᵣ RVal_Bits sp ∗
   "x9" ↦ᵣ RVal_Bits pointer ∗
   base ↦ₘ∗ bytes ∗ writeSuccessHashesScratch sp ∗
   mmio_range 0x2401a0c0 16 ∗ spec_trace tail ∗ P ∗
   ⌜bv_unsigned pointer = (base + 32 * Z.of_nat total)%Z⌝ ∗ True)%I.

Global Instance : LithiumUnfold (@writeSuccessSuffixHashesZeroResources) := I.

Lemma write_success_suffix_hashes_zero_exit_wand
    `{!islaG Sigma} `{!threadG}
    (sp pointer : bv 64) (base : Z) (total : nat)
    (bytes : list (bv 8)) (tail : spec) (P : iProp Sigma) :
  (reg_col zesu_ram_sys_regs ∗
   "x8" ↦ᵣ RVal_Bits (BV 64 0) ∗
   writeSuccessSuffixHashesZeroResources sp pointer base total bytes tail P) -∗
  writeSuccessHashesLoopExit sp base total bytes tail P.
Proof.
  iIntros "(Hsys & H8 & Hrest)".
  iEval (unfold writeSuccessSuffixHashesZeroResources) in "Hrest".
  iDestruct "Hrest" as
    "(Hother & H2 & H9 & Hbytes & Hscratch & Hmmio & Htrace & HP &
      %Hpointer & _)".
  rewrite /writeSuccessHashesLoopExit.
  iExists pointer.
  iFrame "Hsys Hother H2 H8 H9 Hbytes Hscratch Hmmio Htrace HP".
  iPureIntro. constructor; [exact Hpointer | trivial].
Qed.
