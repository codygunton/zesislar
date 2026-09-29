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

Definition writeSuccessExactPostWithdrawalsSecondTail {Decoded}
    (witness : writeSuccessNativeWitness Decoded) : spec :=
  let observation := writeSuccessExactObservation
    (writeSuccessDecodedBytes witness) (writeSuccessValues witness)
    (writeSuccessPayload witness) (writeSuccessTransactions witness)
    (writeSuccessRawTransactions witness) (writeSuccessWithdrawalsBytes witness)
    (writeSuccessWithdrawalsCount witness) (writeSuccessPostData witness) in
  writeOutputPayloadsSpec
    (drop 2 (writeSuccessPost156e8Descriptors
      (writeSuccessFrameSp witness) (writeSuccessPostData witness)))
    (drop 2 (map writeSuccessPrivateBytes (writeSuccessPostFragments observation)))
    (writeSuccessTraceTail witness).

Lemma write_success_exact_post_withdrawals_second_tail {Decoded}
    (witness : writeSuccessNativeWitness Decoded) :
  exactPostWithdrawalsFirstTail witness =
    Snapshots.writeOutputEvents (writeSuccessFrameSp witness - BV 64 16)%bv (BV 64 8)
      (writeSuccessPrivateBytes (writeSuccessEncodeU64
        (bv_unsigned (writeSuccessValueWord (writeSuccessValues witness) 14))))
      (writeSuccessExactPostWithdrawalsSecondTail witness).
Proof.
  unfold exactPostWithdrawalsFirstTail, writeSuccessExactPostWithdrawalsSecondTail,
    writeSuccessPost156e8Descriptors, writeSuccessPostFragments,
    writeSuccessExactObservation, writeSuccessNativeObservation.
  cbn [tl drop map writeOutputPayloadsSpec]. reflexivity.
Qed.
Print Assumptions write_success_exact_post_withdrawals_second_tail.

Definition writeSuccessExactPostWithdrawalsAt15718
    `{!islaG Sigma} `{!threadG} {Decoded}
    `{!WriteSuccessMemoryRepresentation Decoded}
    (args : WriteSuccessArgs Decoded)
    (witness : writeSuccessNativeWitness Decoded) (P : iProp Sigma) : iProp Sigma :=
  let sp := writeSuccessFrameSp witness in
  let values := writeSuccessValues witness in
  (reg_col zesu_ram_sys_regs ∗
   reg_col ((fun register => (KindReg register, BitsShape 64)) <$>
     ["x8"; "x12"; "x13"; "x14"; "x15"]) ∗
   "x1" ↦ᵣ RVal_Bits (BV 64 0x15714) ∗ "x2" ↦ᵣ RVal_Bits sp ∗
   "x5" ↦ᵣ RVal_Bits (BV 64 (mapIoContextAddress defaultMap)) ∗
   "x10" ↦ᵣ RVal_Bits (sp + BV 64 1624)%bv ∗
   "x11" ↦ᵣ RVal_Bits (writeSuccessValueWord values 16) ∗
   "x18" ↦ᵣ RVal_Bits (sp + BV 64 1768)%bv ∗
   "x9" ↦ᵣ RVal_Bits (BV 64 0) ∗
   (bv_unsigned sp + 1624) ↦ₘ writeSuccessValueWord values 15 ∗
   (bv_unsigned sp + 1632) ↦ₘ writeSuccessValueWord values 16 ∗
   reg_col ((fun register => (KindReg register, BitsShape 64)) <$>
     ["x3"; "x4"; "x6"; "x7"; "x16"; "x17";
      "x19"; "x20"; "x21"; "x22"; "x23"; "x24"; "x25"; "x26";
      "x27"; "x28"; "x29"; "x30"; "x31"]) ∗
   bv_unsigned (writeSuccessWithdrawalsBase witness) ↦ₘ∗ writeSuccessWithdrawalsBytes witness ∗
   (bv_unsigned sp + 72) ↦ₘ WriteSuccessPostTransactionResources.writeSuccessPostWord
     (WriteSuccessPostTransactionResources.writeSuccessPostTailWords (writeSuccessDecodedBytes witness)) 7 ∗
   ⌜WriteSuccessPostTransactionResources.writeSuccessPostTransactionDataFacts sp
     (writeSuccessSourceBytes witness) (writeSuccessDecodedBytes witness)
     (writeSuccessPostData witness)⌝ ∗
   (bv_unsigned sp - 48) ↦ₘ? 32 ∗
   (((bv_unsigned sp - 48) ↦ₘ? 32 ∗ (bv_unsigned sp + 1624) ↦ₘ? 16) -∗
     writeSuccessExactPostWithdrawalsMemoryFrame args witness) ∗ P ∗
   (bv_unsigned sp + 1744) ↦ₘ? 48 ∗ (bv_unsigned sp - 16) ↦ₘ? 16 ∗
   mmio_range (machineOutputAddress defaultMap) 16 ∗
   spec_trace (writeSuccessExactPostWithdrawalsSecondTail witness) ∗ True)%I.
Global Instance : LithiumUnfold (@writeSuccessExactPostWithdrawalsAt15718) := I.
