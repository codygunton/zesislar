From Coq Require Import Lists.List ZArith.ZArith.
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Contracts.IslarisMachine.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessCallAbi.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessEvents.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessTransactionsOptionalAddressSome1517cBoundary.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessTransactionsOptionalAddressSome1518cCallEntry.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessTransactionsOptionalAddressSome15190Adapter.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessTransactionsOptionalAddressSome15190Boundary.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessTransactionsOptionalAddressSome1518cCallRegisters.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessTransactionsOptionalAddressSome1518cCallScratch.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessTransactionsOptionalAddressSome1518cCallContinuation.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessTransactionsOptionalAddressSome15170Handoff.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessTransactionsOptionalAddressSomeHandoff.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessTransactionsSpec.

Definition writeSuccessTransactionsOptionalAddressSome1518cCallFrame
    `{!islaG Sigma} `{!threadG} (P : iProp Sigma)
    (sp : bv 64) (base : Z) (transaction : writeSuccessTransaction)
    (transactions processed remaining : list writeSuccessTransaction)
    (bytes prefix suffix : list (bv 8)) (tail : spec) : iProp Sigma :=
  (reg_col zesu_ram_sys_regs ∗
   reg_col writeSuccessTransactions15168OtherRegShapes ∗
   "x1" ↦ᵣ RVal_Bits (BV 64 0x15190) ∗ "x2" ↦ᵣ RVal_Bits sp ∗
   "x5" ↦ᵣ: (fun value => ⌜valu_has_shape value (BitsShape 64)⌝) ∗
   "x12" ↦ᵣ: (fun value => ⌜valu_has_shape value (BitsShape 64)⌝) ∗
   "x8" ↦ᵣ RVal_Bits (writeSuccessTransactionWord transaction 192) ∗
   "x9" ↦ᵣ RVal_Bits (writeSuccessTransactionWord transaction 16) ∗
   "x18" ↦ᵣ RVal_Bits (writeSuccessTransactionWord transaction 48) ∗
   "x19" ↦ᵣ RVal_Bits (writeSuccessTransactionWord transaction 224) ∗
   "x20" ↦ᵣ RVal_Bits (writeSuccessTransactionWord transaction 56) ∗
   "x21" ↦ᵣ RVal_Bits (writeSuccessTransactionWord transaction 72) ∗
   "x22" ↦ᵣ RVal_Bits (writeSuccessTransactionWord transaction 200) ∗
   "x23" ↦ᵣ RVal_Bits (writeSuccessTransactionWord transaction 24) ∗
   "x24" ↦ᵣ RVal_Bits (writeSuccessTransactionWord transaction 8) ∗
   "x25" ↦ᵣ RVal_Bits (writeSuccessTransactionWord transaction 0) ∗
   "x26" ↦ᵣ RVal_Bits (writeSuccessTransactionWord transaction 184) ∗
   "x27" ↦ᵣ RVal_Bits
     (bv_zero_extend 64 (writeSuccessTransactionByte transaction 32)) ∗
   "x10" ↦ᵣ RVal_Bits (sp + BV 64 1744)%bv ∗
   "x11" ↦ᵣ RVal_Bits (BV 64 20) ∗
   writeSuccessTransactionsScratch15174
     sp base transactions processed transaction ∗
   mmio_range 0x2401a0c0 16 ∗
   spec_trace (writeOutputEvents (sp + BV 64 1744)%bv (BV 64 20)
     (writeSuccessTransactionPhaseEvents TransactionValue sp transaction
       (writeSuccessTransactionsEvents sp remaining tail))) ∗
   writeSuccessTransactionsOptionalAddressSomeFrame P sp base transaction
     transactions processed remaining bytes prefix suffix tail ∗
   instr_body 0x15190 (writeSuccessTransactionsOptionalAddressSomeAt15190Spec P) ∗
   True)%I.

Global Typeclasses Opaque writeSuccessTransactionsOptionalAddressSome1518cCallFrame.

Lemma write_success_transactions_optional_address_some_1518c_call_frame
    `{!islaG Sigma} `{!threadG} (P : iProp Sigma)
    (sp : bv 64) (base : Z) (transaction : writeSuccessTransaction)
    (transactions processed remaining : list writeSuccessTransaction)
    (bytes prefix suffix : list (bv 8)) (tail : spec) :
  writeSuccessTransactionsOptionalAddressSome1518cCallFrame P sp base transaction
    transactions processed remaining bytes prefix suffix tail -∗
  writeSuccessTransactionsOptionalAddressSome1518cCallEntry P sp base transaction
    transactions processed remaining bytes prefix suffix tail.
Proof.
  iStartProof. iIntros "Hframe".
  iEval (unfold writeSuccessTransactionsOptionalAddressSome1518cCallFrame)
    in "Hframe".
  iDestruct "Hframe" as
    "(Hsys & Hother & H1 & H2 & H5 & H12 & H8 & H9 & H18 & H19 & H20 & H21 &
      H22 & H23 & H24 & H25 & H26 & H27 & H10 & H11 & Hscratch & Hmmio &
      Htrace & Hframe & Hnext & _)".
  iAssert (reg_col [(KindReg "x3", BitsShape 64); (KindReg "x4", BitsShape 64)] ∗
    reg_col ((fun r => (KindReg r, BitsShape 64)) <$> tmp_registers) ∗
    "x12" ↦ᵣ: (fun value => ⌜valu_has_shape value (BitsShape 64)⌝) ∗
    "x13" ↦ᵣ: (fun value => ⌜valu_has_shape value (BitsShape 64)⌝) ∗
    "x14" ↦ᵣ: (fun value => ⌜valu_has_shape value (BitsShape 64)⌝) ∗
    "x15" ↦ᵣ: (fun value => ⌜valu_has_shape value (BitsShape 64)⌝) ∗
    "x16" ↦ᵣ: (fun value => ⌜valu_has_shape value (BitsShape 64)⌝) ∗
    "x17" ↦ᵣ: (fun value => ⌜valu_has_shape value (BitsShape 64)⌝))%I
    with "[Hother H5 H12]" as "Hregisters".
  { iApply (write_success_transactions_optional_address_some_1518c_call_registers).
    iFrame. }
  iDestruct "Hregisters" as
    "(H34 & Htmp & H12 & H13 & H14 & H15 & H16 & H17)".
  iAssert (writeSuccessTransactionsOptionalAddressSome15190Frame P sp base
    transaction transactions processed remaining bytes prefix suffix tail ∗
    ⌜bv_unsigned sp `mod` 16 = 0⌝ ∗
    ⌜0x20000000 <= bv_unsigned sp - 16⌝ ∗
    ⌜bv_unsigned sp < 0x40000000⌝)%I
    with "[H34 Hscratch Hframe]" as "HscratchOut".
  { iApply (write_success_transactions_optional_address_some_1518c_call_scratch
      P sp base transaction transactions processed remaining bytes prefix suffix tail).
    iFrame. }
  iDestruct "HscratchOut" as
    "(Hframe15190 & %Halign & %Hlower & %Hupper)".
  iPoseProof (write_success_transactions_optional_address_some_1518c_call_continuation
    P sp base transaction transactions processed remaining bytes prefix suffix tail
    ) as "HretWand".
  iSpecialize ("HretWand" with "Hnext").
  iSpecialize ("HretWand" with "Hframe15190").
  iRename "HretWand" into "HretPre".
  have HstackLower : (0x20000000 <= bv_unsigned sp - 16)%Z by lia.
  have HstackUpper : (bv_unsigned sp < 0x40000000)%Z by lia.
  rewrite /writeSuccessTransactionsOptionalAddressSome1518cCallEntry.
  iFrame "Hsys Htmp H10 H11 H12 H13 H14 H15 H16 H17 H8 H9 H18 H19 H20 H21
    H22 H23 H24 H25 H26 H27 H1 H2 Hmmio Htrace HretPre".
  iSplit; first (iPureIntro; exact Halign).
  iSplit; first (iPureIntro; exact HstackLower).
  iSplit; first (iPureIntro; exact HstackUpper).
  done.
Qed.
