Require Import ZesuSsz.Automation.All.
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Contracts.IslarisMachine.
From ZesuSsz.Proofs.WriteSuccess Require Import
  WriteSuccessBlobHashesSpec WriteSuccessLoopCommon WriteSuccessExactBlobHashesModel
  WriteSuccessExactBlobHashesLoopReturn WriteSuccessExactBlobHashesTail
  WriteSuccessExactBlobHashesTailRegisters WriteSuccessExactStorageKeysCounter.

Definition writeSuccessExactBlobHashesLoopSpec `{!islaG Sigma} `{!threadG}
    (sp : bv 64) (base : Z) (total : nat) (bytes : list (bv 8))
    (tail : spec) (P : iProp Sigma) : iProp Sigma :=
  (∃ (pointer : bv 64) (processed remaining : nat),
    reg_col zesu_ram_sys_regs ∗ reg_col writeSuccessBlobHashesOtherRegShapes ∗
    "x2" ↦ᵣ RVal_Bits sp ∗ "x19" ↦ᵣ RVal_Bits pointer ∗
    "x22" ↦ᵣ RVal_Bits (Z_to_bv 64 (Z.of_nat (S remaining))) ∗
    base ↦ₘ∗ bytes ∗ writeSuccessBlobHashesScratch sp ∗ mmio_range 0x2401a0c0 16 ∗
    spec_trace (writeSuccessExactBlobHashesEvents sp processed (S remaining) bytes tail) ∗ P ∗
    writeSuccessFixedWidthArrayInvariant sp pointer base total processed remaining bytes ∗
    instr_pre 0x15564 (writeSuccessBlobHashesLoopExit sp base total bytes tail P) ∗ True)%I.
Global Instance : LithiumUnfold (@writeSuccessExactBlobHashesLoopSpec) := I.

Lemma blob_tail_positive `{!islaG Sigma} `{!threadG}
    (sp pointer : bv 64) base total processed remaining bytes tail (P : iProp Sigma) :
  (blobTailState (pointer + BV 64 32)%bv (Z_to_bv 64 (Z.of_nat (S remaining))) (Z_to_bv 64 (Z.of_nat (S remaining)) - BV 64 1)%bv
    (blobTailFrame sp pointer base total processed remaining bytes tail P) ∗
   ⌜(Z_to_bv 64 (Z.of_nat (S remaining)) - BV 64 1)%bv <> BV 64 0⌝ ∗ True)%I -∗
  writeSuccessExactBlobHashesLoopSpec sp base total bytes tail P.
Proof.
  rewrite storage_keys_counter_decrement.
  iIntros "(Hstate & %Hnonzero & _)".
  destruct remaining as [|remaining]; [exfalso; apply Hnonzero; apply bv_eq; reflexivity|].
  iEval (unfold blobTailState, blobTailFrame, writeSuccessFixedWidthArrayInvariant) in "Hstate".
  iDestruct "Hstate" as
    "(Hsys & Hpointer & Hsaved & Hcountreg &
      (Hregs & Hsp & Harray & Hscratch & Hmmio & Htrace & HP &
        (%Htotal & %Hlength & %Hposition & %Hbound & %Halign & %Hsplow & %Hsphigh & %Hbaselow & %Hbasehigh & _) & Hexit & _) & _)".
  iPoseProof (blob_tail_registers with "[Hregs Hsaved]") as "Hother". { iFrame. }
  have Hadvance : bv_unsigned (pointer + BV 64 32)%bv = base + 32 * Z.of_nat (S processed).
  { clear Hbound. apply storage_keys_pointer_advance; [lia|lia|exact Hposition]. }
  have Hnewbound : (S remaining < 2 ^ 64)%nat :=
    Nat.lt_trans _ _ _ (Nat.lt_succ_diag_r _) Hbound.
  iEval (unfold writeSuccessExactBlobHashesLoopSpec).
  iExists (pointer + BV 64 32)%bv, (S processed), remaining.
  iFrame. iEval (unfold writeSuccessFixedWidthArrayInvariant).
  repeat iSplit; try (iPureIntro; first [assumption | clear Hbound Hnewbound; lia]); done.
Qed.
Print Assumptions blob_tail_positive.
