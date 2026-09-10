Require Import ZesuSsz.Automation.All.
From Coq Require Import Lists.List ZArith.ZArith.
Require Import isla.riscv64.riscv64.
From IslaTraces.write_success_blocks Require Import
  Index HintsHashesLoop HintsBlobHashesLoop HintsStorageKeysLoop.
Require Import ZesuSsz.Contracts.IslarisMachine.
Require Import ZesuSsz.Contracts.IslarisCode.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccess.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessCalls.

Import ListNotations.

Local Remove Hints subsume_instr_pre'_inst : typeclass_instances.
Local Existing Instance subsume_instr_pre_wand_inst | 1.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessLoopCommon.
#[local] Hint Extern 7
  (FindInContext (FindInstrKind ?address ?later) FICSyntactic) =>
  let reduced := eval vm_compute in address in
  first [ constr_eq address reduced; fail 1
        | change (FindInContext (FindInstrKind reduced later) FICSyntactic);
          typeclasses eauto ] : typeclass_instances.

Fixpoint writeSuccessHashesEvents (sp : bv 64) (count : nat)
    (tail : spec) : spec :=
  match count with
  | O => tail
  | S count =>
      writeOutputEvents (sp + BV 64 1744)%bv (BV 64 32)
        (writeSuccessHashesEvents sp count tail)
  end.

Definition writeSuccessHashesOtherRegisters : list string :=
  ["x1"; "x3"; "x4"; "x5"; "x6"; "x7";
   "x10"; "x11"; "x12"; "x13"; "x14"; "x15"; "x16"; "x17";
   "x18"; "x19"; "x20"; "x21"; "x22"; "x23"; "x24"; "x25";
   "x26"; "x27"; "x28"; "x29"; "x30"; "x31"].

Definition writeSuccessHashesOtherRegShapes : list (reg_kind * valu_shape) :=
  (fun register => (KindReg register, BitsShape 64))
    <$> writeSuccessHashesOtherRegisters.

Definition writeSuccessHashesScratch `{!islaG Sigma}
    (sp : bv 64) : iProp Sigma :=
  (∃ word0 word1 word2 word3 : bv 64,
    (bv_unsigned sp + 1744) ↦ₘ word0 ∗
    (bv_unsigned sp + 1752) ↦ₘ word1 ∗
    (bv_unsigned sp + 1760) ↦ₘ word2 ∗
    (bv_unsigned sp + 1768) ↦ₘ word3 ∗ True)%I.

Global Instance : LithiumUnfold (@writeSuccessHashesScratch) := I.

Definition writeSuccessHashesLoopExit `{!islaG Sigma} `{!threadG}
    (sp : bv 64) (base : Z) (total : nat) (bytes : list (bv 8))
    (tail : spec) (P : iProp Sigma) : iProp Sigma :=
  (∃ pointer : bv 64,
    reg_col zesu_ram_sys_regs ∗
    reg_col writeSuccessHashesOtherRegShapes ∗
    "x2" ↦ᵣ RVal_Bits sp ∗ "x8" ↦ᵣ RVal_Bits (BV 64 0) ∗
    "x9" ↦ᵣ RVal_Bits pointer ∗
    base ↦ₘ∗ bytes ∗ writeSuccessHashesScratch sp ∗
    mmio_range 0x2401a0c0 16 ∗ spec_trace tail ∗ P ∗
    ⌜bv_unsigned pointer = (base + 32 * Z.of_nat total)%Z⌝ ∗ True)%I.

Global Instance : LithiumUnfold (@writeSuccessHashesLoopExit) := I.

Definition writeSuccessHashesLoopSpec `{!islaG Sigma} `{!threadG}
    (P : iProp Sigma) : iProp Sigma :=
  (∃ (sp pointer : bv 64) (base : Z)
      (total processed remaining : nat) (bytes : list (bv 8))
      (tail : spec),
    reg_col zesu_ram_sys_regs ∗
    reg_col writeSuccessHashesOtherRegShapes ∗
    "x2" ↦ᵣ RVal_Bits sp ∗
    "x8" ↦ᵣ RVal_Bits (Z_to_bv 64 (Z.of_nat (S remaining))) ∗
    "x9" ↦ᵣ RVal_Bits pointer ∗
    base ↦ₘ∗ bytes ∗ writeSuccessHashesScratch sp ∗
    mmio_range 0x2401a0c0 16 ∗
    spec_trace (writeSuccessHashesEvents sp (S remaining) tail) ∗ P ∗
    writeSuccessFixedWidthArrayInvariant
      sp pointer base total processed remaining bytes ∗
    instr_pre 0x158e0
      (writeSuccessHashesLoopExit sp base total bytes tail P) ∗ True)%I.

Global Instance : LithiumUnfold (@writeSuccessHashesLoopSpec) := I.


Lemma write_success_hashes_word3 `{!islaG Sigma} `{!threadG}
    (P : iProp Sigma) :
  instr_lookup_resources IslaTraces.write_success_blocks.Index.lookup -∗
  IslaTraces.write_success_blocks.Index.spec_instr_resources -∗
  instr_body 0x157b0 (writeSuccessHashesLoopSpec P) -∗
  instr_body 0x15754 (writeSuccessHashesLoopSpec P).
Proof.
  move => *.
  iStartProof.
  iIntros "_ #Hlookup #Hcode Hnext".
  iEval (unfold IslaTraces.write_success_blocks.Index.spec_instr_resources)
    in "Hcode".
  do 2000 liAStep.
  liARun.
  iExists
    (tail, bytes, processed, (processed + S remaining)%nat, base, tt)ₗ.
  liARun.
  Unshelve.
  all: prepare_sidecond.
  all: try (apply bv_eq; rewrite bv_and_unsigned; assumption).
  all: try (bv_simplify_arith H1; bv_solve).
Qed.

Lemma write_success_hashes_word2 `{!islaG Sigma} `{!threadG}
    (P : iProp Sigma) :
  instr_lookup_resources IslaTraces.write_success_blocks.Index.lookup -∗
  IslaTraces.write_success_blocks.Index.spec_instr_resources -∗
  instr_body 0x1580c (writeSuccessHashesLoopSpec P) -∗
  instr_body 0x157b0 (writeSuccessHashesLoopSpec P).
Proof.
  move => *.
  iStartProof.
  iIntros "_ #Hlookup #Hcode Hnext".
  iEval (unfold IslaTraces.write_success_blocks.Index.spec_instr_resources)
    in "Hcode".
  liARun.
  iExists
    (tail, bytes, processed, (processed + S remaining)%nat, base, tt)ₗ.
  liARun.
  Unshelve.
  all: prepare_sidecond.
  all: try (apply bv_eq; rewrite bv_and_unsigned; assumption).
  all: try (bv_simplify_arith H1; bv_solve).
Qed.

Lemma write_success_hashes_word1 `{!islaG Sigma} `{!threadG}
    (P : iProp Sigma) :
  instr_lookup_resources IslaTraces.write_success_blocks.Index.lookup -∗
  IslaTraces.write_success_blocks.Index.spec_instr_resources -∗
  instr_body 0x15868 (writeSuccessHashesLoopSpec P) -∗
  instr_body 0x1580c (writeSuccessHashesLoopSpec P).
Proof.
  move => *.
  iStartProof.
  iIntros "_ #Hlookup #Hcode Hnext".
  iEval (unfold IslaTraces.write_success_blocks.Index.spec_instr_resources)
    in "Hcode".
  liARun.
  iExists
    (tail, bytes, processed, (processed + S remaining)%nat, base, tt)ₗ.
  liARun.
  Unshelve.
  all: prepare_sidecond.
  all: try (apply bv_eq; rewrite bv_and_unsigned; assumption).
  all: try (bv_simplify_arith H1; bv_solve).
Qed.

Lemma write_success_hashes_word0 `{!islaG Sigma} `{!threadG}
    (P : iProp Sigma) :
  instr_lookup_resources IslaTraces.write_success_blocks.Index.lookup -∗
  IslaTraces.write_success_blocks.Index.spec_instr_resources -∗
  instr_body 0x158c4 (writeSuccessHashesLoopSpec P) -∗
  instr_body 0x15868 (writeSuccessHashesLoopSpec P).
Proof.
  move => *.
  iStartProof.
  iIntros "_ #Hlookup #Hcode Hnext".
  iEval (unfold IslaTraces.write_success_blocks.Index.spec_instr_resources)
    in "Hcode".
  liARun.
  iExists
    (tail, bytes, processed, (processed + S remaining)%nat, base, tt)ₗ.
  liARun.
  Unshelve.
  all: prepare_sidecond.
  all: try (apply bv_eq; rewrite bv_and_unsigned; assumption).
  all: try (bv_simplify_arith H1; bv_solve).
Qed.

Lemma write_success_hashes_tail `{!islaG Sigma} `{!threadG}
    (P : iProp Sigma) :
  instr_lookup_resources IslaTraces.write_success_blocks.Index.lookup -∗
  IslaTraces.write_success_blocks.Index.spec_instr_resources -∗
  □ instr_pre 0x10190 zesuWriteOutputCallSpec -∗
  □ instr_pre 0x15754 (writeSuccessHashesLoopSpec P) -∗
  instr_body 0x158c4 (writeSuccessHashesLoopSpec P).
Proof.
  move => *.
  iStartProof.
  iIntros "_ #Hlookup #Hcode #Houtput #Hloop".
  iEval (unfold IslaTraces.write_success_blocks.Index.spec_instr_resources)
    in "Hcode".
  liARun.
  destruct remaining as [|remaining'].
  - exfalso. apply H14. bv_solve.
  - iExists
      (tail, bytes, remaining', S processed,
       (processed + S (S remaining'))%nat, base,
       (pointer + BV 64 32)%bv, tt)ₗ.
    liARun.
  Unshelve.
  all: prepare_sidecond.
  all: try (apply bv_eq; rewrite bv_and_unsigned; assumption).
  all: try (bv_simplify_arith H1; bv_solve).
  all: try lia.
  all: try iFrame.
  all: have Hremaining : remaining = O by
    (bv_simplify_arith H14; bv_solve).
  all: subst remaining.
  all: cbn.
  all: try reflexivity.
  all: try (bv_simplify_arith H1; bv_solve).
Qed.

Lemma write_success_hashes_loop `{!islaG Sigma} `{!threadG}
    (P : iProp Sigma) :
  instr_lookup_resources IslaTraces.write_success_blocks.Index.lookup -∗
  IslaTraces.write_success_blocks.Index.spec_instr_resources -∗
  □ instr_pre 0x10190 zesuWriteOutputCallSpec -∗
  □ instr_pre 0x15754 (writeSuccessHashesLoopSpec P) -∗
  instr_body 0x15754 (writeSuccessHashesLoopSpec P).
Proof.
  iStartProof. iIntros "#Hlookup #Hcode #Houtput #Hloop".
  iApply (write_success_hashes_word3 P with "Hlookup Hcode").
  iApply (write_success_hashes_word2 P with "Hlookup Hcode").
  iApply (write_success_hashes_word1 P with "Hlookup Hcode").
  iApply (write_success_hashes_word0 P with "Hlookup Hcode").
  iApply (write_success_hashes_tail P with
    "Hlookup Hcode Houtput Hloop").
Qed.

Lemma write_success_hashes_loop_pre `{!islaG Sigma} `{!threadG}
    (P : iProp Sigma) :
  instr_lookup_resources IslaTraces.write_success_blocks.Index.lookup -∗
  IslaTraces.write_success_blocks.Index.spec_instr_resources -∗
  □ instr_pre 0x10190 zesuWriteOutputCallSpec -∗
  □ instr_pre 0x15754 (writeSuccessHashesLoopSpec P).
Proof.
  iStartProof. iIntros "#Hlookup #Hcode #Houtput".
  iLöb as "IH".
  iModIntro. iApply instr_pre_to_body. iNext.
  iApply (write_success_hashes_loop P with "Hlookup Hcode Houtput IH").
Qed.
