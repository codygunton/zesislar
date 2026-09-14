Require Import ZesuSsz.Automation.All.
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Contracts.IslarisMachine.
Require Import ZesuSsz.Export.Snapshots.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessExactBooleanSpec.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessOutputSemantic.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessObservation.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessExactOptionalU64SomeBooleanResume.
From ZesuSsz.Proofs.WriteSuccess Require Import
  WriteSuccessExactOptionalU64SomeCall WriteSuccessExactOptionalU64SomeCallSpec
  WriteSuccessExactOptionalU64SomeJumpHandoff WriteSuccessExactTransactionsChainSomeCall.
From IslaTraces.write_success_35 Require Import instrs.
Local Remove Hints IslaTraces.write_success_35.a150f8_spec.a150f8_spec_inst : typeclass_instances.

Definition optionalU64SomeExactCallerContext `{!islaG Sigma} `{!threadG}
    (pointer value sp ret old_x5 old_x6 old_x8 : bv 64)
    (bytes : list (bv 8)) (tail : spec) (P : iProp Sigma) : iProp Sigma :=
  ("x5" ↦ᵣ RVal_Bits old_x5 ∗ "x6" ↦ᵣ RVal_Bits old_x6 ∗
   mmio_range 0x2401a0c0 16 ∗
   spec_trace (writeOutputEvents (sp - BV 64 25)%bv (BV 64 1)
     (writeSuccessBooleanWordPayload (BV 64 1))
     (writeOutputEvents (sp - BV 64 16)%bv (BV 64 8)
       (writeSuccessPrivateBytes (writeSuccessEncodeU64 (bv_unsigned value))) tail)) ∗
   ⌜bv_extract 0 4 sp = BV 4 0⌝ ∗ ⌜bv_unsigned sp `mod` 16 = 0⌝ ∗
   ⌜0x20000000 <= bv_unsigned sp - 32⌝ ∗ ⌜bv_unsigned sp < 0x40000000⌝ ∗
   ⌜bv_extract 0 1 ret = BV 1 0⌝ ∗ ⌜bv_extract 1 1 ret = BV 1 0⌝ ∗
   ⌜bv_extract 0 2 ret = BV 2 0⌝ ∗ P ∗ True)%I.

Global Instance : LithiumUnfold (@optionalU64SomeExactCallerContext) := I.

Definition transactionChainSomeCaller `{!islaG Sigma} `{!threadG}
    (value sp oldra olddata old5 old6 old8 old11 : bv 64)
    (tag : bv 8) (bytes : list (bv 8)) tail (P : iProp Sigma) : iProp Sigma :=
  (reg_col zesu_ram_sys_regs ∗
   "x1" ↦ᵣ RVal_Bits oldra ∗ "x2" ↦ᵣ RVal_Bits sp ∗
   "x8" ↦ᵣ RVal_Bits old8 ∗ "x10" ↦ᵣ RVal_Bits olddata ∗
   "x11" ↦ᵣ RVal_Bits old11 ∗ bv_unsigned (sp + BV 64 1664)%bv ↦ₘ∗ bytes ∗
   (bv_unsigned sp - 32) ↦ₘ? 32 ∗
   ⌜bytes !! 8%nat = Some tag⌝ ∗ ⌜tag <> BV 8 0⌝ ∗
   ⌜value = Z_to_bv 64 (little_endian_to_bv 8 (take 8 bytes))⌝ ∗
   ⌜(8 <= length bytes)%nat⌝ ∗ ⌜bv_extract 0 3 (sp + BV 64 1664)%bv = BV 3 0⌝ ∗
   ⌜0x20000000 <= bv_unsigned (sp + BV 64 1664)%bv⌝ ∗
   ⌜bv_unsigned (sp + BV 64 1664)%bv + Z.of_nat (length bytes) < 0x40000000⌝ ∗
   ⌜bv_extract 0 4 sp = BV 4 0⌝ ∗
   ⌜0x20000000 <= bv_unsigned sp - 32⌝ ∗ ⌜bv_unsigned sp < 0x40000000⌝ ∗
   optionalU64SomeExactCallerContext (sp + BV 64 1664)%bv value sp (BV 64 0x150fc)
     old5 old6 old8 bytes tail P ∗ True)%I.
Global Instance : LithiumUnfold (@transactionChainSomeCaller) := I.


Lemma transactions_chain_some_caller_entry `{!islaG Sigma} `{!threadG}
    value sp oldra olddata old5 old6 old8 old11 tag bytes tail (P : iProp Sigma) :
  □ instr_pre 0x150fc (optionalU64SomeExactPost sp (BV 64 0x150fc) old8 tail
    (optionalU64SomeExactSourceFrame (sp + BV 64 1664)%bv bytes P)) -∗
  transactionChainSomeCaller value sp oldra olddata old5 old6 old8 old11 tag bytes tail P -∗
  transactionChainSomeEntry value sp oldra olddata old5 old6 old8 old11 tag bytes tail P.
Proof.
  iStartProof. iIntros "#Hnext Hcaller".
  iEval (rewrite /transactionChainSomeCaller) in "Hcaller".
  iEval (rewrite /transactionChainSomeEntry).
  iDestruct "Hcaller" as "(Hsys & H1 & H2 & H8 & H10 & H11 & Hbytes & Hstack &
    Htag & Hnonzero & Hvalue & Hlength & Halign & Hmin & Hmax & Hsp & Hlow & Hhigh & Hcontext & _)".
  iEval (rewrite /optionalU64SomeExactCallerContext) in "Hcontext".
  iEval (rewrite /optionalU64SomeExactCallContext).
  iDestruct "Hcontext" as "(H5 & H6 & Hmmio & Htrace & Hsp4 & Hmod & Hmin2 & Hmax2 &
    Hret0 & Hret1 & Hret2 & HP & _)".
  iFrame. iSplit; last done. iExact "Hnext".
Qed.
Print Assumptions transactions_chain_some_caller_entry.
