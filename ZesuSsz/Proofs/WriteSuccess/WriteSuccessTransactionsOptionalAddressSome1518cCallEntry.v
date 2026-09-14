Require Import ZesuSsz.Automation.All.
Require Import ZesuMachineMap.Machine.
From Coq Require Import Lists.List ZArith.ZArith.
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Contracts.IslarisMachine.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessCalls.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessCallAbi.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessEvents.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessTransactionsOptionalAddressSome15190Boundary.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessTransactionsSpec.

Definition writeSuccessTransactionsOptionalAddressSome1518cCallEntry
    `{!islaG Sigma} `{!threadG} (P : iProp Sigma)
    (sp : bv 64) (base : Z) (transaction : writeSuccessTransaction)
    (transactions processed remaining : list writeSuccessTransaction)
    (bytes prefix suffix : list (bv 8)) (tail : spec) : iProp Sigma :=
  (reg_col zesu_ram_sys_regs ∗
   reg_col ((fun r => (KindReg r, BitsShape 64)) <$> tmp_registers) ∗
   "x10" ↦ᵣ RVal_Bits (sp + BV 64 1744)%bv ∗
   "x11" ↦ᵣ RVal_Bits (BV 64 20) ∗
   "x12" ↦ᵣ: (fun value => ⌜valu_has_shape value (BitsShape 64)⌝) ∗
   "x13" ↦ᵣ: (fun value => ⌜valu_has_shape value (BitsShape 64)⌝) ∗
   "x14" ↦ᵣ: (fun value => ⌜valu_has_shape value (BitsShape 64)⌝) ∗
   "x15" ↦ᵣ: (fun value => ⌜valu_has_shape value (BitsShape 64)⌝) ∗
   "x16" ↦ᵣ: (fun value => ⌜valu_has_shape value (BitsShape 64)⌝) ∗
   "x17" ↦ᵣ: (fun value => ⌜valu_has_shape value (BitsShape 64)⌝) ∗
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
   "x1" ↦ᵣ RVal_Bits (BV 64 0x15190) ∗ "x2" ↦ᵣ RVal_Bits sp ∗
   mmio_range (machineOutputAddress defaultMap) 16 ∗
   spec_trace (writeOutputEventsAny (sp + BV 64 1744)%bv (BV 64 20)
     (writeSuccessTransactionPhaseEvents TransactionValue sp transaction
       (writeSuccessTransactionsEvents sp remaining tail))) ∗
   instr_pre 0x15190
     (zesu_c_call_ret 0
       [RVal_Bits (writeSuccessTransactionWord transaction 192);
        RVal_Bits (writeSuccessTransactionWord transaction 16);
        RVal_Bits (writeSuccessTransactionWord transaction 48);
        RVal_Bits (writeSuccessTransactionWord transaction 224);
        RVal_Bits (writeSuccessTransactionWord transaction 56);
        RVal_Bits (writeSuccessTransactionWord transaction 72);
        RVal_Bits (writeSuccessTransactionWord transaction 200);
        RVal_Bits (writeSuccessTransactionWord transaction 24);
        RVal_Bits (writeSuccessTransactionWord transaction 8);
        RVal_Bits (writeSuccessTransactionWord transaction 0);
        RVal_Bits (writeSuccessTransactionWord transaction 184);
        RVal_Bits (bv_zero_extend 64 (writeSuccessTransactionByte transaction 32))]
       (BV 64 0x15190) sp
       (fun _ => mmio_range (machineOutputAddress defaultMap) 16 ∗
         spec_trace (writeSuccessTransactionPhaseEvents TransactionValue sp transaction
           (writeSuccessTransactionsEvents sp remaining tail)) ∗ True)) ∗
   ⌜bv_unsigned sp `mod` 16 = 0⌝ ∗
   ⌜(mapRamBase defaultMap) <= bv_unsigned sp - 16⌝ ∗
   ⌜bv_unsigned sp < (machineRamEnd defaultMap)⌝ ∗ True)%I.

Global Typeclasses Opaque writeSuccessTransactionsOptionalAddressSome1518cCallEntry.

Lemma write_success_transactions_optional_address_some_1518c_call_entry
    `{!islaG Sigma} `{!threadG} (P : iProp Sigma)
    (sp : bv 64) (base : Z) (transaction : writeSuccessTransaction)
    (transactions processed remaining : list writeSuccessTransaction)
    (bytes prefix suffix : list (bv 8)) (tail : spec) :
  writeSuccessTransactionsOptionalAddressSome1518cCallEntry P sp base transaction
    transactions processed remaining bytes prefix suffix tail -∗
  zesuWriteOutputCallSpec.
Proof.
  iStartProof. iIntros "Hentry".
  iEval (unfold writeSuccessTransactionsOptionalAddressSome1518cCallEntry)
    in "Hentry".
  iDestruct "Hentry" as
    "(Hsys & Htmp & H10 & H11 & H12 & H13 & H14 & H15 & H16 & H17 & H8 & H9 &
      H18 & H19 & H20 & H21 & H22 & H23 & H24 & H25 & H26 & H27 & H1 & H2 &
      Hmmio & Htrace & HretPre & %Halign & %Hlower & %Hupper & _)".
  iEval (rewrite reg_mapsto_pred_eq /reg_mapsto_pred_def) in "H12 H13 H14 H15 H16 H17".
  iDestruct "H12" as (v12) "(H12 & %Hv12)".
  apply (proj2 (simpl_impl (P := valu_has_shape v12 (BitsShape 64))
    (Ps := ∃ b12 : bv 64, v12 = RVal_Bits b12))) in Hv12.
  destruct Hv12 as (b12 & ->).
  iDestruct "H13" as (v13) "(H13 & %Hv13)".
  apply (proj2 (simpl_impl (P := valu_has_shape v13 (BitsShape 64))
    (Ps := ∃ b13 : bv 64, v13 = RVal_Bits b13))) in Hv13.
  destruct Hv13 as (b13 & ->).
  iDestruct "H14" as (v14) "(H14 & %Hv14)".
  apply (proj2 (simpl_impl (P := valu_has_shape v14 (BitsShape 64))
    (Ps := ∃ b14 : bv 64, v14 = RVal_Bits b14))) in Hv14.
  destruct Hv14 as (b14 & ->).
  iDestruct "H15" as (v15) "(H15 & %Hv15)".
  apply (proj2 (simpl_impl (P := valu_has_shape v15 (BitsShape 64))
    (Ps := ∃ b15 : bv 64, v15 = RVal_Bits b15))) in Hv15.
  destruct Hv15 as (b15 & ->).
  iDestruct "H16" as (v16) "(H16 & %Hv16)".
  apply (proj2 (simpl_impl (P := valu_has_shape v16 (BitsShape 64))
    (Ps := ∃ b16 : bv 64, v16 = RVal_Bits b16))) in Hv16.
  destruct Hv16 as (b16 & ->).
  iDestruct "H17" as (v17) "(H17 & %Hv17)".
  apply (proj2 (simpl_impl (P := valu_has_shape v17 (BitsShape 64))
    (Ps := ∃ b17 : bv 64, v17 = RVal_Bits b17))) in Hv17.
  destruct Hv17 as (b17 & ->).
  iEval (unfold zesuWriteOutputCallSpec, zesu_c_call).
  iExists sp, (BV 64 0x15190).
  iEval (rewrite !reg_mapsto_pred_eq /reg_mapsto_pred_def).
  iFrame "Hsys Htmp H10 H11 H12 H13 H14 H15 H16 H17 H8 H9 H18 H19 H20 H21
    H22 H23 H24 H25 H26 H27 H1 H2 Hmmio Htrace HretPre".
  repeat (iSplit; first (iPureIntro; cbn; done)).
  iExists b12. iSplit; first done.
  iExists b13. iSplit; first done.
  iExists b14. iSplit; first done.
  iExists b15. iSplit; first done.
  iExists b16. iSplit; first done.
  iExists b17. iSplit; first done.
  repeat iSplit; try iPureIntro; try assumption; try bv_solve; try lia;
    try iFrame.
  all: try (cbn; done).
  all: try (rewrite mem_mapsto_uninit_0; iPureIntro; bv_solve).
  all: try (iPureIntro; exact Halign).
  all: try (iPureIntro; lia).
  Unshelve.
  all: try (rewrite mem_mapsto_uninit_0; iPureIntro; bv_solve).
  all: try (iPureIntro; exact Halign).
  all: try (iPureIntro; lia).
Qed.
