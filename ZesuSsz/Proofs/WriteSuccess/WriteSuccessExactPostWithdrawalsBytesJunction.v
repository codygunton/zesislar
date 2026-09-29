Require Import ZesuSsz.Automation.All.
Require Import isla.riscv64.riscv64.
Require Import ZesuSsz.Contracts.Endpoints.
From ZesuSsz.Proofs.WriteSuccess Require Import
  WriteSuccessNativeContract WriteSuccessRepresentation WriteSuccessValueSpec
  WriteSuccessOutputSemantic WriteSuccessPostTransactionDescriptors.
Require Import ZesuSsz.Automation.Sets.v2.
Require Import ZesuSsz.Automation.Switches.ReturnBundle.
Require Import ZesuSsz.Automation.Switches.ArrayLoadPriority.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessExactPrefixStackFacts.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessExactPostWithdrawalsChainEnd.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessExactPostWithdrawalsSplit.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessExactPostWithdrawalsPrefixJunction.
Require Import ZesuSsz.Proofs.WriteSuccess.Interfaces.
From IslaTraces.write_success_blocks Require Import Index.

Require Import ZesuSsz.Automation.Switches.LoadedTrace.
Require Import ZesuSsz.Proofs.WriteSuccess.InterfacesCoverage.
Require Import ZesuSsz.Automation.Switches.ConjunctMatch.

Require Import ZesuSsz.Export.Snapshots.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessObservation.
Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessExactTrace.

Require Import ZesuSsz.Proofs.WriteSuccess.WriteSuccessExactPostWithdrawalsBytesFacts.

Definition writeSuccessExactPostWithdrawalsAt1571c
    `{!islaG Sigma} `{!threadG} {Decoded}
    `{!WriteSuccessMemoryRepresentation Decoded}
    (args : WriteSuccessArgs Decoded)
    (witness : writeSuccessNativeWitness Decoded) (P : iProp Sigma) : iProp Sigma :=
  let sp := writeSuccessFrameSp witness in
  (reg_col zesu_ram_sys_regs ∗
   "x1" ↦ᵣ RVal_Bits (BV 64 0x1571c) ∗ "x2" ↦ᵣ RVal_Bits sp ∗
   "x5" ↦ᵣ RVal_Bits (BV 64 (mapIoContextAddress defaultMap)) ∗
   reg_col ((fun register => (KindReg register, BitsShape 64)) <$>
     ["x6"; "x8"; "x10"; "x11"; "x12"; "x13"; "x14"; "x15"]) ∗
   "x18" ↦ᵣ RVal_Bits (sp + BV 64 1768)%bv ∗ "x9" ↦ᵣ RVal_Bits (BV 64 0) ∗
   reg_col ((fun register => (KindReg register, BitsShape 64)) <$>
     ["x3"; "x4"; "x7"; "x16"; "x17";
      "x19"; "x20"; "x21"; "x22"; "x23"; "x24"; "x25"; "x26";
      "x27"; "x28"; "x29"; "x30"; "x31"]) ∗
   bv_unsigned (writeSuccessWithdrawalsBase witness) ↦ₘ∗ writeSuccessWithdrawalsBytes witness ∗
   (bv_unsigned sp + 72) ↦ₘ WriteSuccessPostTransactionResources.writeSuccessPostWord
     (WriteSuccessPostTransactionResources.writeSuccessPostTailWords (writeSuccessDecodedBytes witness)) 7 ∗
   writeSuccessExactPostWithdrawalsMemoryFrame args witness ∗ P ∗
   (bv_unsigned sp + 1744) ↦ₘ? 48 ∗ (bv_unsigned sp - 16) ↦ₘ? 16 ∗
   mmio_range (machineOutputAddress defaultMap) 16 ∗
   spec_trace (pw_binding_declared witness) ∗ True)%I.
Global Instance : LithiumUnfold (@writeSuccessExactPostWithdrawalsAt1571c) := I.

Lemma write_success_post_withdrawals_optional_memory_restore
    `{!islaG Sigma} `{!threadG} {Decoded}
    `{!WriteSuccessMemoryRepresentation Decoded}
    (args : WriteSuccessArgs Decoded) (witness : writeSuccessNativeWitness Decoded) :
  (((bv_unsigned (writeSuccessFrameSp witness) - 48) ↦ₘ? 32 ∗
    (bv_unsigned (writeSuccessFrameSp witness) + 1624) ↦ₘ? 16) -∗
    writeSuccessExactPostWithdrawalsMemoryFrame args witness) -∗
  (bv_unsigned (writeSuccessFrameSp witness) - 48) ↦ₘ? 16 -∗
  (bv_unsigned (writeSuccessFrameSp witness) - 32) ↦ₘ? 32 -∗
  (bv_unsigned (writeSuccessFrameSp witness) + 1624) ↦ₘ? 16 -∗
  writeSuccessExactPostWithdrawalsMemoryFrame args witness ∗
    (bv_unsigned (writeSuccessFrameSp witness) - 16) ↦ₘ? 16.
Proof.
  iIntros "Hrestore Hlow Hreturn Hoptional".
  iDestruct (mem_mapsto_uninit_split 16 with "Hreturn") as "[Hmiddle Hsmall]"; [lia |].
  iEval (replace (bv_unsigned (writeSuccessFrameSp witness) - 32)%Z with
    (bv_unsigned (writeSuccessFrameSp witness) - 48 + 16)%Z by lia) in "Hmiddle".
  iPoseProof (mem_mapsto_uninit_combine 16 (bv_unsigned (writeSuccessFrameSp witness) - 48) (DfracOwn 1) 32
    ltac:(lia) with "Hlow Hmiddle") as "Hscratch".
  iPoseProof ("Hrestore" with "[$Hscratch $Hoptional]") as "Hmemory".
  iEval (replace (bv_unsigned (writeSuccessFrameSp witness) - 32 + 16)%Z with
    (bv_unsigned (writeSuccessFrameSp witness) - 16)%Z by lia) in "Hsmall".
  iFrame.
Qed.
Print Assumptions write_success_post_withdrawals_optional_memory_restore.
